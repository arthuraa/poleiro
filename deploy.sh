#!/bin/bash

make
. deploy.config.sh
rsync -r _site/ "${SERVER}:public_html/poleiro/"
ssh $SERVER 'chmod -R o+rx public_html/poleiro'
