#!/usr/bin/env ruby
# -*- coding: utf-8 -*-
#
# Ruby script to generate README.agda
#
# Usage:
# 1. install ruby
# 2. install yaml gem
# 3. `ruby generate-README.rb`
# -. [optional] have a look at README.agda.
# 4. `./agdaCheck.sh`

readme_name = "README"

# What to put at the start of README
header = %Q{\
module #{readme_name} where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * multiple calculi
}

# `bugs` are unchecked
ignore = /^bugs\./

# Documentation highlights
# CAUTION: Do not assume any order of module listing!
documentation = {

"Denotation.Derive.Canon-Popl14" =>
  "Correctness theorem for canonical derivation of Calc. Popl14",

"Denotation.Derive.Optimized-Popl14" =>
  "Correctness theorem for optimized derivation of Calc. Popl14",

"Denotation.Specification.Canon-Popl14" =>
  "Denotation-as-specification for canonical derivation of Calc. Popl14",

"Denotation.Implementation.Popl14" =>
  "The idea of implementing a denotational " +
   "specification for Calc. Popl14",

"Syntax.Language.Atlas" =>
  "Language definition of Calc. Atlas",

"Syntax.Term.Plotkin" =>
%q{Terms of a calculus described in Plotkin style
  - types are parametric in base types
  - terms are parametric in constants
  This style of language description is employed in:
  G. D. Plotkin. "LCF considered as a programming language."
  Theoretical Computer Science 5(3) pp. 223--255, 1997.
  http://dx.doi.org/10.1016/0304-3975(77)90044-5},
}

agda_base_dir = File.dirname(File.expand_path(__FILE__))
ext = '.agda'
agda_readme = File.join(agda_base_dir, "#{readme_name}#{ext}")

agda_files = `cd #{agda_base_dir} && find . -name "*#{ext}"`

agda_modules = agda_files.lines.map{ |line|
  mod_path = line.match(/^\.\/(.*)#{ext}$/)[1]
  raise "Error when parsing:\n#{line}" if mod_path.nil?
  mod_path.gsub(File::SEPARATOR, '.')
}

def comment(readme, doc)
  readme.puts("{- #{doc} -}")
end

def import(readme, mod)
  readme.puts("import #{mod}")
end

File.open(agda_readme, 'w') { |readme|
  readme.write(header)
  readme.puts
  agda_modules.each { |mod|
    next if mod == readme_name
    next if mod =~ ignore
    doc = documentation[mod]
    comment(readme, doc) unless doc.nil?
    import(readme, mod)
  }
}
