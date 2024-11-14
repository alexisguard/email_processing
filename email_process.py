import os
import sys
import extract_msg
import json
import logging
import hashlib
from pathlib import Path
from datetime import datetime
from typing import Dict, Any, Union, Optional, BinaryIO, List
from dataclasses import dataclass, field
import shutil
import time
from concurrent.futures import ThreadPoolExecutor, TimeoutError
from tqdm import tqdm
from fpdf import FPDF
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
from reportlab.lib.units import inch
import re
import tempfile
import uuid
import os
import subprocess

def truncate_filename(self, filename: str, max_length: int = 255) -> str:
    if len(filename) > max_length:
        base, ext = os.path.splitext(filename)
        filename = base[:max_length - len(ext)] + ext
    return filename

def setup_logging():
    """Configure le système de logging."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler('email_extraction.log', encoding='utf-8'),
            logging.StreamHandler(sys.stdout)
        ]
    )
    
    # Filtrer les messages de log spécifiques
    logging.getLogger('extract_msg').setLevel(logging.ERROR)

from typing import List  # Assurez-vous que List est importé

class ContactHandler:
    @staticmethod
    def parse_contact(contact_str: Optional[str]) -> List[Dict[str, str]]:
        """
        Parse les informations de contact de manière avancée.
        
        Retourne une liste de dictionnaires avec nom, email, et type de contact.
        """
        if not contact_str:
            return []
        
        contacts = []
        # Séparation des contacts multiples
        contact_list = contact_str.split(';') if ';' in contact_str else [contact_str]
        
        for contact in contact_list:
            contact = contact.strip()
            parsed_contact = {
                "raw": contact,
                "name": "",
                "email": "",
                "type": "unknown"
            }
            
            # Extraction de l'email entre < >
            email_match = re.search(r'<(.+?)>', contact)
            if email_match:
                parsed_contact["email"] = email_match.group(1).strip()
                # Nom est ce qui précède l'email
                parsed_contact["name"] = contact.split('<')[0].strip()
            else:
                # Si pas de format <email>, traiter comme email direct
                parsed_contact["email"] = contact
                parsed_contact["name"] = contact
            
            contacts.append(parsed_contact)
        
        return contacts

@dataclass
class Config:
    MAX_PATH_LENGTH: int = 240
    MAX_FILENAME_LENGTH: int = 100
    MAX_DEPTH: int = 1
    CHUNK_SIZE: int = 8192
    # Correction : utiliser default_factory pour la liste
    ENCODING_FALLBACKS: List[str] = field(default_factory=lambda: ["utf-8", "latin1", "cp1252"])
    MAX_ATTACHMENT_SIZE: int = 100 * 1024 * 1024  # 100MB
    TIMEOUT: int = 30  # 30 secondes par opération
    CLEAN_SPECIAL_CHARS: bool = True

class PathHandler:
	@staticmethod
	def get_hash(content: str, length: int = 8) -> str:
		"""Génère un hash court pour un contenu donné."""
		return hashlib.md5(content.encode()).hexdigest()[:length]

	@staticmethod
	def sanitize_filename(filename: str) -> str:
		"""Nettoie les caractères spéciaux des noms de fichiers."""
		if not Config.CLEAN_SPECIAL_CHARS:
			return filename
			
		char_map = {
			'é': 'e', 'è': 'e', 'ê': 'e', 'ë': 'e',
			'à': 'a', 'â': 'a', 'ä': 'a',
			'î': 'i', 'ï': 'i',
			'ô': 'o', 'ö': 'o',
			'ù': 'u', 'û': 'u', 'ü': 'u',
			'ç': 'c',
			' ': '_'
		}
		
		clean_name = ''.join(char_map.get(c.lower(), c) for c in filename)
		clean_name = ''.join(c for c in clean_name if c.isalnum() or c in '_-.')
		return clean_name or "unnamed_file"

	@staticmethod
	def clean_filename(filename: str, max_length: int = Config.MAX_FILENAME_LENGTH) -> str:
		"""Nettoie et tronque un nom de fichier si nécessaire."""
		if not filename:
			return "unnamed_file"

		clean_name = PathHandler.sanitize_filename(filename)
		
		if len(clean_name) > max_length:
			name, ext = os.path.splitext(clean_name)
			hash_str = PathHandler.get_hash(name)
			clean_name = f"{name[:max_length-12]}_{hash_str}{ext}"

		return clean_name

	@staticmethod
	def truncate_path(path: Union[str, Path], max_length: int = Config.MAX_PATH_LENGTH) -> Path:
		"""Tronque un chemin tout en gardant sa validité."""
		path = Path(path)
		if len(str(path)) <= max_length:
			return path

		parent = path.parent
		stem = path.stem
		suffix = path.suffix
		hash_str = PathHandler.get_hash(stem)
		
		available_length = max_length - len(str(parent)) - len(suffix) - len(hash_str) - 2
		
		if available_length < 10:
			return parent / f"{hash_str}{suffix}"
			
		truncated = f"{stem[:available_length]}_{hash_str}{suffix}"
		return parent / truncated

	@staticmethod
	def ensure_directory(path: Union[str, Path]) -> Path:
		"""Crée un dossier et tous ses parents si nécessaire."""
		path = Path(path)
		try:
			path.mkdir(parents=True, exist_ok=True)
			return path
		except OSError as e:
			if "too long" in str(e).lower():
				truncated = PathHandler.truncate_path(path)
				truncated.mkdir(parents=True, exist_ok=True)
				return truncated
			raise

	@staticmethod
	def get_unique_path(path: Union[str, Path]) -> Path:
		"""Génère un chemin unique en ajoutant un suffixe si nécessaire."""
		path = Path(path)
		if not path.exists():
			return path

		counter = 1
		while True:
			new_path = path.parent / f"{path.stem}_{counter}{path.suffix}"
			if not new_path.exists():
				return new_path
			counter += 1

class EmailExtractor:
	def __init__(self):
		self.path_handler = PathHandler()
		self.processed_paths = set()
		self.progress_bar = None
		self.attachment_progress = None
		self.encodings = ["utf-8", "latin1", "cp1252"]
		
	def __enter__(self):
		return self
		
	def __exit__(self, exc_type, exc_val, exc_tb):
		if self.progress_bar:
			self.progress_bar.close()
		if self.attachment_progress:
			self.attachment_progress.close()
	
	def enrich_message_body(self, body: str) -> str:
		"""
		Enrichit le corps du message en identifiant et formatant les contacts.
		"""
		if not body:
			return body
		
		# Expressions régulières pour identifier les emails
		email_pattern = r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b'
		
		def replace_email(match):
			email = match.group(0)
			return f"[Email: {email}]"
		
		# Remplacer les emails par un format plus lisible
		enriched_body = re.sub(email_pattern, replace_email, body)
		
		return enriched_body
		
	def save_as_pdf(self, data: Dict[str, Any], path: Path) -> bool:
		"""Sauvegarde les données en PDF avec support Unicode complet et détails étendus."""
		try:
			# Création du document
			doc = SimpleDocTemplate(
				str(path),
				pagesize=A4,
				rightMargin=72,
				leftMargin=72,
				topMargin=72,
				bottomMargin=72
			)
			
			# Styles
			styles = getSampleStyleSheet()
			title_style = styles['Heading1']
			normal_style = styles['Normal']
			label_style = ParagraphStyle(
				'LabelStyle',
				parent=styles['Normal'],
				fontName='Helvetica-Bold'
			)
			
			# Construction du contenu
			story = []
			
			# Titre
			story.append(Paragraph("Details de l'email", title_style))
			story.append(Spacer(1, 12))
			
			# Fonction pour formater les informations de contact
			def format_contact_info(contact_str: Optional[str]) -> str:
				"""Formate les informations de contact pour une meilleure lisibilité."""
				if not contact_str:
					return "N/A"
				
				# Séparer les différents contacts
				contacts = contact_str.split(';')
				formatted_contacts = []
				
				for contact in contacts:
					contact = contact.strip()
					# Essayer d'extraire le nom et l'email
					if '<' in contact and '>' in contact:
						name = contact.split('<')[0].strip()
						email = contact.split('<')[1].split('>')[0].strip()
						formatted_contacts.append(f"{name} ({email})")
					else:
						formatted_contacts.append(contact)
				
				return '; '.join(formatted_contacts)
			
			def escape_pdf_text(text: str) -> str:
				"""Échappe les caractères spéciaux pour le PDF"""
				if not text:
					return "N/A"
				return (text
					.replace('&', '&amp;')
					.replace('<', '&lt;')
					.replace('>', '&gt;')
					.replace('"', '&quot;')
					.replace("'", '&#39;')
					.strip() or "N/A")

			# Métadonnées avec échappement
			metadata_fields = [
				("De", format_contact_info(data.get("from"))),
				("A", format_contact_info(data.get("to"))),
				("CC", format_contact_info(data.get("cc"))),
				("Sujet", escape_pdf_text(data.get("subject"))),
				("Date", escape_pdf_text(data.get("date"))),
				("Date de traitement", escape_pdf_text(data.get("processed_date")))
			]
			
			for label, value in metadata_fields:
				if value:
					# Formatage du texte avec label en gras
					text = f"<b>{label}:</b> {value}"
					story.append(Paragraph(text, normal_style))
					story.append(Spacer(1, 6))
			
			# Corps du message
			story.append(Spacer(1, 12))
			story.append(Paragraph("Corps du message:", styles['Heading2']))
			story.append(Spacer(1, 12))
			
			body = data.get("body", "")
			if body:
				# Nettoyage et préparation du texte
				body_text = str(body).replace('\r', '\n')
				paragraphs = body_text.split('\n')
				
				for paragraph in paragraphs:
					if paragraph.strip():
						story.append(Paragraph(paragraph.strip(), normal_style))
						story.append(Spacer(1, 6))
			
			# Génération du PDF
			doc.build(story)
			return True
			
		except Exception as e:
			logging.error(f"Erreur fatale lors de la sauvegarde PDF: {str(e)}")
			return False

	def save_json(self, data: Dict[str, Any], path: Path) -> bool:
			"""Sauvegarde les données en JSON avec gestion des encodages."""
			try:
				for encoding in self.encodings:
					try:
						with open(path, 'w', encoding=encoding) as f:
							json.dump(data, f, indent=4, ensure_ascii=False)
						return True
					except UnicodeEncodeError:
						continue
					except Exception as e:
						logging.error(f"Erreur lors de la sauvegarde JSON ({encoding}): {str(e)}")
						continue

				# Fallback en ASCII si aucun autre encodage ne fonctionne
				with open(path, 'w', encoding='ascii') as f:
					json.dump(data, f, indent=4, ensure_ascii=True)
				return True

			except Exception as e:
				logging.error(f"Erreur fatale lors de la sauvegarde JSON: {str(e)}")
				return False

	def save_attachment(self, attachment, save_path: Path, depth: int = 0) -> bool:
		"""
		Sauvegarde des pièces jointes avec gestion différenciée des types.
		"""
		try:
			# Gestion spécifique pour les pièces jointes de type EmbeddedMsgAttachment
			if isinstance(attachment, extract_msg.attachments.emb_msg_att.EmbeddedMsgAttachment):
				try:
					# Vérifier si c'est un message incorporé valide
					if hasattr(attachment, 'msg') and isinstance(attachment.msg, extract_msg.Message):
						embedded_msg = attachment.msg
						# Générer un nom de fichier pour le message incorporé avec l'extension .msg
						filename = self.path_handler.clean_filename(
							embedded_msg.subject or "Email_En_Piece_Jointe"
						) + ".msg"
						# Définir le chemin complet vers le fichier de destination
						destination_path = save_path.parent / filename
						destination_path = self.path_handler.get_unique_path(destination_path)
						# Sauvegarder le message incorporé à l'emplacement souhaité
						embedded_msg.save(customPath=str(destination_path))
						logging.info(f"Message incorporé sauvegardé à : {destination_path}")
						
						# Traiter le message incorporé de manière récursive
						self.process_msg(embedded_msg, save_path.parent, depth=depth + 1)
						return True
					else:
						logging.error("L'EmbeddedMsgAttachment ne contient pas de message valide.")
						return False
				except Exception as emb_error:
					logging.error(f"Erreur lors de la sauvegarde de l'EmbeddedMsgAttachment: {str(emb_error)}")
					return False
			
			# Traitement des autres types de pièces jointes
			else:
				# Extraction des données de la pièce jointe
				try:
					data = attachment.data
					logging.info("Données extraites via .data")
				except AttributeError:
					try:
						data = attachment.get_data()
						logging.info("Données extraites via .get_data()")
					except Exception as data_error:
						logging.error(f"Impossible d'extraire les données : {data_error}")
						return False
				
				# Sauvegarde des données dans le fichier
				with open(save_path, 'wb') as f:
					f.write(data)
				logging.info(f"Pièce jointe sauvegardée : {save_path}")
				return True
		
		except Exception as e:
			logging.error(f"Erreur fatale lors de la sauvegarde de la pièce jointe: {str(e)}")
			return False

	def extract_emails_from_attachment(self, attachment) -> List[str]:
		"""
		Extrait les emails potentiels d'une pièce jointe.
		"""
		try:
			# Conversion des données en texte
			text = ""
			try:
				text = attachment.data.decode('utf-8')
			except:
				try:
					text = attachment.data.decode('latin-1')
				except:
					return []
			
			# Expression régulière pour trouver les emails
			email_pattern = r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Z|a-z]{2,}\b'
			emails = re.findall(email_pattern, text)
			
			return list(set(emails))
		
		except Exception as e:
			logging.error(f"Erreur lors de l'extraction des emails: {str(e)}")
			return []

	def _write_chunks(self, file: BinaryIO, data: bytes) -> None:
		for i in range(0, len(data), Config.CHUNK_SIZE):
			chunk = data[i:i + Config.CHUNK_SIZE]
			file.write(chunk)
			if self.attachment_progress:
				self.attachment_progress.update(len(chunk))
	
	def generate_file_map(self, root_dir: Path) -> bool:
		"""Génère une carte des fichiers et dossiers au format JSON."""
		try:
			def build_tree(path: Path) -> Dict:
				"""Construit récursivement l'arborescence des fichiers."""
				if path.is_file():
					return {
						"type": "file",
						"name": path.name,
						"size": path.stat().st_size,
						"modified": datetime.fromtimestamp(path.stat().st_mtime).isoformat()
					}
				
				tree = {
					"type": "directory",
					"name": path.name,
					"children": []
				}
				
				try:
					for item in path.iterdir():
						tree["children"].append(build_tree(item))
				except PermissionError:
					logging.warning(f"Permission refusée pour accéder à {path}")
				
				return tree

			# Construction de l'arborescence
			file_map = build_tree(root_dir)
			
			# Sauvegarde dans un fichier JSON
			output_path = root_dir / "file_map.json"
			with open(output_path, 'w', encoding='utf-8') as f:
				json.dump(file_map, f, indent=2, ensure_ascii=False)
				
			return True
		
		except Exception as e:
			logging.error(f"Erreur lors de la génération de la carte des fichiers: {str(e)}")
			return False

	def process_msg(self, msg_file: Union[str, Path, extract_msg.Message], output_dir: Path, depth: int = 0) -> bool:
		"""Traite un fichier MSG et ses pièces jointes, en maintenant la relation entre emails et pièces jointes sans créer de chemins trop longs."""
		if depth >= Config.MAX_DEPTH:
			logging.warning(f"Profondeur maximale ({Config.MAX_DEPTH}) atteinte lors du traitement de {msg_file}")
			return False

		def format_contacts(contact_str: Optional[str]) -> str:
			contacts = ContactHandler.parse_contact(contact_str)
			return "; ".join([
				f"{c['name']} <{c['email']}>" for c in contacts if c['email']
			])

		try:
			msg = (msg_file if isinstance(msg_file, extract_msg.Message) 
					else extract_msg.Message(str(msg_file)))

			try:
				# Récupérer le nom du fichier MSG
				msg_filename = Path(str(msg_file)).stem if isinstance(msg_file, (str, Path)) else "Email_Sans_Nom"
				
				# Utiliser le nom du fichier MSG pour le dossier
				folder_name = self.path_handler.clean_filename(msg_filename)
				unique_id = uuid.uuid4().hex[:8]
				
				folder_name = f"{folder_name}_{unique_id}"

				email_folder = self.path_handler.get_unique_path(output_dir / folder_name)
				email_folder.mkdir(parents=True, exist_ok=True)
				logging.info(f"Dossier créé: {email_folder}")

				def escape_special_chars(text: str) -> str:
						"""Échappe les caractères spéciaux"""
						if not text:
							return ""
						return (text
							.replace('&', '&amp;')
							.replace('<', '&lt;')
							.replace('>', '&gt;')
							.replace('"', '&quot;')
							.replace("'", '&#39;')
							.replace(':', '_')
							.replace('/', '_')
							.replace('\\', '_')
							.strip())

				# Échapper les caractères spéciaux dans le sujet
				subject = escape_special_chars(msg.subject) if msg.subject else "Email_Sans_Sujet"
				folder_name = self.path_handler.clean_filename(subject)
				unique_id = uuid.uuid4().hex[:8]
				folder_name = f"{folder_name}_{unique_id}"

				metadata = {
					"from": format_contacts(msg.sender),
					"to": format_contacts(msg.to),
					"cc": format_contacts(msg.cc) if hasattr(msg, 'cc') else None,
					"subject": msg_filename,
					"date": str(msg.date),
					"body": self.enrich_message_body(msg.body),
					"processed_date": datetime.now().isoformat()
				}

				# Utiliser le même nom pour le PDF
				metadata_path = email_folder / f"{msg_filename}.msg.pdf"
				if not self.save_as_pdf(metadata, metadata_path):
					return False

				if msg.attachments:
					# Sauvegarder les pièces jointes directement dans le dossier de l'email
					for attachment in msg.attachments:
						try:
							logging.info(f"Type de pièce jointe: {type(attachment)}")
							logging.info(f"Classe de la pièce jointe: {attachment.__class__}")

							filename = self.path_handler.clean_filename(
								getattr(attachment, 'longFilename', '') or 
								getattr(attachment, 'shortFilename', '') or 
								"unnamed_attachment"
							)

							# Générer un nom de fichier unique pour éviter les collisions
							unique_filename = f"{uuid.uuid4().hex[:8]}_{filename}"
							save_path = self.path_handler.get_unique_path(
								email_folder / unique_filename
							)

							# Sauvegarde de la pièce jointe
							if not self.save_attachment(attachment, save_path, depth=depth):
								logging.warning(f"Échec de la sauvegarde de {filename}")
								continue

							# Traiter les messages incorporés
							if isinstance(attachment, extract_msg.attachments.emb_msg_att.EmbeddedMsgAttachment):
								embedded_msg = attachment.msg
								# Traiter le message incorporé en utilisant le même dossier
								self.process_msg(embedded_msg, email_folder, depth=depth + 1)

						except Exception as e:
							logging.error(f"Erreur lors du traitement de {filename}: {str(e)}")
							continue

				self.generate_file_map(output_dir)

				return True

			finally:
				if isinstance(msg_file, str):
					try:
						msg.close()
					except:
						pass

			if self.progress_bar is not None:
				self.progress_bar.set_description(f"Traité: {folder_name}")
				self.progress_bar.update(0)

			return True

		except Exception as e:
			logging.error(f"Erreur lors du traitement de {msg_file}: {str(e)}")
			return False
	
	def convert_txt_to_pdf(self, txt_path: Path) -> bool:
		"""
		Convertit un fichier texte en PDF en utilisant le nom du dossier parent.

		Args:
			txt_path (Path): Chemin du fichier texte à convertir

		Returns:
			bool: True si la conversion réussit, False sinon
		"""
		try:
			# Vérifier que le fichier est bien message.txt
			if txt_path.name.lower() != 'message.txt':
				logging.warning(f"Le fichier {txt_path} n'est pas message.txt")
				return False
			
			# Récupérer le nom du dossier parent pour nommer le PDF
			pdf_name = txt_path.parent.name + '.msg.pdf'
			pdf_path = txt_path.parent / pdf_name
			
			# Lire le contenu du fichier texte
			try:
				with open(txt_path, 'r', encoding='utf-8') as f:
					text_content = f.read()
			except UnicodeDecodeError:
				# Essayer d'autres encodages si utf-8 échoue
				for encoding in ['latin1', 'cp1252']:
					try:
						with open(txt_path, 'r', encoding=encoding) as f:
							text_content = f.read()
						break
					except:
						continue
				else:
					logging.error(f"Impossible de lire {txt_path} avec un encodage connu")
					return False
			
			def escape_html(text: str) -> str:
				"""Échappe les caractères HTML spéciaux"""
				return (text
					.replace('&', '&amp;')
					.replace('<', '&lt;')
					.replace('>', '&gt;')
					.replace('"', '&quot;')
					.replace("'", '&#39;'))
			
			# Création du document PDF
			doc = SimpleDocTemplate(
				str(pdf_path),
				pagesize=A4,
				rightMargin=72,
				leftMargin=72,
				topMargin=72,
				bottomMargin=72
			)
			
			# Styles
			styles = getSampleStyleSheet()
			normal_style = styles['Normal']
			heading_style = styles['Heading1']
			
			# Construction du contenu
			story = []
			
			# Diviser le texte en lignes
			lines = text_content.split('\n')
			
			# Traiter chaque ligne
			for line in lines:
				line = line.strip()
				if line:
					# Échapper les caractères HTML spéciaux
					escaped_line = escape_html(line)
					# Texte standard
					story.append(Paragraph(escaped_line, normal_style))
					# Ajouter un petit espace entre les paragraphes
					story.append(Spacer(1, 6))
			
			# Génération du PDF
			doc.build(story)
			
			logging.info(f"Conversion de {txt_path} en PDF réussie : {pdf_path}")
			return True

		except Exception as e:
			logging.error(f"Erreur lors de la conversion de {txt_path} en PDF: {str(e)}")
			return False

def clear_directory(directory: Path):
    """Supprime récursivement tous les fichiers et dossiers dans un répertoire."""
    try:
        for item in directory.iterdir():
            if item.is_dir():
                shutil.rmtree(item)
            else:
                item.unlink()
        logging.info(f"Répertoire {directory} vidé avec succès")
    except Exception as e:
        logging.error(f"Erreur lors du nettoyage du répertoire {directory}: {str(e)}")

def main():
    """Point d'entrée principal avec gestion complète des erreurs."""
    setup_logging()

    try:
        source_folder = Path("mails")  # Chemin mis à jour pour macOS
        output_dir = Path("EXTRACTED_EMAILS")

        if not source_folder.exists():
            logging.error(f"Dossier source {source_folder} inexistant")
            return

        # Nettoyer le dossier de sortie avant le traitement
        PathHandler.ensure_directory(output_dir)
        clear_directory(output_dir)

        msg_files = list(source_folder.glob('*.msg'))

        if not msg_files:
            logging.warning(f"Pas de fichiers MSG dans {source_folder}")
            return

        with EmailExtractor() as extractor:
            with tqdm(total=len(msg_files), desc="Extraction des emails", 
                      bar_format="{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]") as pbar:
                extractor.progress_bar = pbar
                
                for msg_file in msg_files:
                    try:
                        result = extractor.process_msg(msg_file, output_dir)
                        pbar.update(1)
                        if not result:
                            pbar.set_description(f"Échec: {msg_file.name}")
                    except Exception as e:
                        logging.error(f"Erreur lors du traitement de {msg_file.name}: {str(e)}")
                        pbar.update(1)
		
		# Traiter tous les fichiers message.txt après le traitement des MSG
        with EmailExtractor() as extractor:
            txt_files = list(output_dir.rglob('message.txt'))
            if txt_files:
                with tqdm(total=len(txt_files), desc="Conversion des message.txt", 
                          bar_format="{l_bar}{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]") as pbar:
                    for txt_path in txt_files:
                        try:
                            result = extractor.convert_txt_to_pdf(txt_path)
                            pbar.update(1)
                            if not result:
                                pbar.set_description(f"Échec: {txt_path.name}")
                        except Exception as e:
                            logging.error(f"Erreur lors de la conversion de {txt_path}: {str(e)}")
                            pbar.update(1)

    except Exception as e:
        logging.critical(f"Erreur critique: {str(e)}")
        raise

if __name__ == '__main__':
    main()