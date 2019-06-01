#!/bin/sh

fswatch slides.lhs sep.lhs sep.bib | xargs -I{} make
