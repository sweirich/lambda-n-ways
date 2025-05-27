#!/bin/bash

# Script to iterate through variables, change a line in a file, execute make, and move files.
# The script will revert the haskell file after running make eval
# and generate an xlsx file from the results.

# Function to display usage instructions.
usage() {
  echo "Usage: $0 [-h]"
  echo "  -h, --help      Display this help message."
  echo "  -b, --branch X  Branch in Rebound repo."
  echo ""
  echo "  This script will iterate through predefined variables, changing the line"
  echo "  'import Rebound.Env.Internal' in ../Rebound/src/Rebound/Env.hs,"
  echo "  executing 'make normalize', moving files accordingly, generating txt files"
  exit 1
}

# Define the file to modify.
file="../rebound/src/Rebound/Env.hs"
# define the branch to use
branch="wip/phantom-snat-fin-vec"

# Parse command-line options.
while [[ $# -gt 0 ]]; do
  key="$1"
  case "$key" in
    -h|--help)
      usage
      ;;
    *)
      usage
      exit 1
      ;;
  esac
done


# Check if the file exists.
if [ ! -f "$file" ]; then
  echo "Error: File '$file' not found."
  exit 1
fi


pushd "../rebound"; git checkout "$branch"; popd

# Define the list of variables.
valid_variables=("Internal" "InternalA" "Functional" "InternalB" "InternalLazy" "Vector")

# Iterate through the variables.
for variable in "${valid_variables[@]}"; do
  # Use sed to change the line.  Use a different sed syntax.
  new_string="import Rebound.Env.$variable"
  sed -i -e "s/import Rebound.Env.Internal/$new_string/" "$file"

  # Check the exit status of sed.
  if [ $? -ne 0 ]; then
    echo "Error: Failed to change line in '$file' for variable '$variable'."
    exit 1
  fi

  echo "Successfully changed line in '$file' to '$new_string'."

  # Execute 'make eval'.
  make normalize
  if [ $? -ne 0 ]; then
    echo "Error: 'make normalize' failed for variable '$variable'."
    # Revert the file even if make eval fails
    sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
    exit 1
  fi

  echo "'make eval' executed successfully for variable '$variable'."

  # Move files.
  source_dir="results/Stephanie-Weirich-MBP/rebound_strict_envV"
  dest_dir="results/ablate/rebound_strict_envV/$branch/$variable"

  # Check if the source directory exists.
  if [ ! -d "$source_dir" ]; then
    echo "Error: Source directory '$source_dir' not found for variable '$variable'."
    # Revert the file even if the directory is not found
    sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
    exit 1
  fi

  # Create the destination directory if it doesn't exist.
  mkdir -p "$dest_dir"
  if [ $? -ne 0 ]; then
    echo "Error: Failed to create destination directory '$dest_dir' for variable '$variable'."
    # Revert the file even if directory creation fails
    sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
    exit 1
  fi

  # Move the files 
  mv $source_dir/* $dest_dir/
  # find "$source_dir" -type f -exec sh -c 'mv "$1" "${1%.txt}.csv"' _ {} \;
  if [ $? -ne 0 ]; then
    echo "Error: Failed to move files from '$source_dir' to '$dest_dir' and convert to CSV for variable '$variable'."
    # Revert the file even if file moving fails.
    sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
    exit 1
  fi
  echo "Successfully moved and converted files to CSV in '$dest_dir' for variable '$variable'."

  # Revert the Haskell file to its original state.
  sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
  if [ $? -ne 0 ]; then
    echo "Error: Failed to revert the Haskell file '$file' after processing variable '$variable'."
    exit 1
  fi
  echo "Successfully reverted '$file' to its original state after processing variable '$variable'."

done

exit 0
