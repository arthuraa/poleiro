#!/bin/bash

make
. deploy.config.sh
rsync -r _site/ "${SERVER}:/var/www/poleiro"
