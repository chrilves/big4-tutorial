#!/bin/sh

# Coq
find Coq \( -iname "*.glob" -or -iname "*.vo" -or -iname "*.aux" \) -delete

# Agda
find Agda \( -iname "*.agdai" \) -delete
rm -fr Agda/MAlonzo

# Idris
find Idris \( -iname "*.ibc" -or -iname "*.js" \) -delete

# FStar
