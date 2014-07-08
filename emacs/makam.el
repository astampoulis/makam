;; makam.el - Proof General for Makam.

(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'makam "Makam"

 proof-prog-name		     "/home/antonis/work/mit/makam/makam"
 proof-script-command-end-regexp     "\\.[ \n\r\t]\\|\\?[ \n\r\t]"        ;; end of commands
 proof-script-comment-start          "(*"	;; comments
 proof-script-comment-end            "*)"	;; comments
 proof-shell-annotated-prompt-regexp "# " ;; matches prompts

 proof-shell-strip-crs-from-input nil
 proof-script-fly-past-comments  t

 proof-shell-error-regexp        "^.*Exception:\\|^.*failure\\|^.*Error:\\|^.*Failure:\\|^.*Camlp4:\\|^In .*:\\|Unchaught OCaml-level exception.*\\.\\|^Parsing error at\\|^Error in staged code"
 proof-shell-interrupt-regexp        "^.*Interrupted."
 proof-shell-result-start            ""
 proof-shell-result-end              "#"
 proof-shell-restart                 "%%reset.\n"
 proof-forget-id-command             "%%forget %s.\n"
 proof-shell-handle-output-system-specific
    '(lambda (cmd string) (proof-shell-display-output-as-response
			     proof-shell-delayed-output-flags
			     string))
    
 ;; next setting is just to prevent warning
 proof-save-command-regexp	proof-no-regexp
 )

(provide 'makam)

