import os
import re

# Define the base directory for the paper
sections_dir = os.path.join(os.path.dirname(__file__), '..', 'paper', 'section')

# Mapping of large files to their new subdirectories
files_to_split = {
    'appendix_soundness.tex': 'soundness',
    'appendix_case_studies.tex': 'case_studies'
}

def sanitize_filename(title):
    """Converts a LaTeX subsection title to a safe filename."""
    # Remove common LaTeX commands that don't contribute to the name
    title = re.sub(r'\\(p|code|label)\{.*?\}', '', title)
    # Remove other non-alphanumeric characters, except for spaces
    title = re.sub(r'[^\w\s-]', '', title).strip()
    # Replace spaces with underscores and convert to lowercase
    return title.replace(' ', '_').lower() + '.tex'

def split_file(source_filename, target_subdir):
    """Splits a single .tex file by its subsections."""
    source_path = os.path.join(sections_dir, source_filename)
    target_dir = os.path.join(sections_dir, target_subdir)

    print(f"Processing {source_filename} -> {target_dir}/")

    try:
        with open(source_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except FileNotFoundError:
        print(f"  [ERROR] Source file not found: {source_path}")
        return

    # Find all subsection commands. We assume they are the primary delimiter.
    subsection_regex = re.compile(r'\\subsection\*?\{(.*?)\}', re.DOTALL)
    matches = list(subsection_regex.finditer(content))

    if not matches:
        print(f"  [WARNING] No subsections found in {source_filename}. Nothing to split.")
        return

    for i, match in enumerate(matches):
        subsection_title = match.group(1)
        start_pos = match.start()
        
        # The end position is the start of the next subsection, or the end of the file
        end_pos = matches[i+1].start() if i + 1 < len(matches) else len(content)
        
        subsection_content = content[start_pos:end_pos].strip()
        new_filename = sanitize_filename(subsection_title)
        output_path = os.path.join(target_dir, new_filename)

        print(f"  -> Writing subsection '{subsection_title.strip()}' to {new_filename}")
        try:
            with open(output_path, 'w', encoding='utf-8') as f_out:
                f_out.write(subsection_content + '\n')
        except IOError as e:
            print(f"    [ERROR] Could not write to file: {e}")

def main():
    """Main splitting function."""
    print("Starting subsection splitting process...\n")
    for filename, subdir in files_to_split.items():
        split_file(filename, subdir)
    print("\nSplitting complete.")

if __name__ == "__main__":
    main()
