#!/bin/bash
function usage()
{
    echo "$0 <smt2 file> <dest_directory>

Splits a query file created using symbooglix's --log-queries="
exit 1
}

if [ $# -ne 2 ]; then
    usage
fi

SMT2_FILE="$1"
DEST_DIR="$2"

if [ ! -f "${SMT2_FILE}" ]; then
    echo "File \"${SMT2_FILE}\" does not exist"
    exit 1
fi

if [ ! -d "${DEST_DIR}" ]; then
    echo "Destination directory \"${DEST_DIR}\" does not exist"
    exit 1
fi

SMT2_FILE_ABS=$(readlink -f "${SMT2_FILE}")
DEST_DIR_ABS=$(readlink -f "${DEST_DIR}")

echo "SMT2 file: ${SMT2_FILE_ABS}"
echo "Dest dir: ${DEST_DIR_ABS}"

# Compute prefix name for files
PREFIX=$(basename "${SMT2_FILE_ABS}")
PREFIX=${PREFIX%.smt2}
echo "prefix:${PREFIX}"

cd "${DEST_DIR_ABS}"
if [ $? -ne 0 ]; then
    echo "Couldn't cd into directory \"${DEST_DIR_ABS}\""
    exit 1
fi

# FIXME: 7 digits may not be enough
csplit --prefix="${PREFIX}-" \
       --suffix='%07d.smt2' \
       --elide-empty-files \
       "${SMT2_FILE_ABS}" \
       '/(exit)/+1' '{*}'
