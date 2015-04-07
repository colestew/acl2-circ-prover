(defun {{modelName}} ({{#inputs}}{{name}} {{/inputs}})
  (let* (
{{#logicGates}}
         ({{output}} ({{modelId}}{{#inputs}} {{id}}{{/inputs}}))
{{/logicGates}}
{{#blocks}}
{{#nthOutputs}}
         ({{id}} (nth {{nthId}} ({{modelId}}{{#inputs}} {{id}}{{/inputs}})))
{{/nthOutputs}}
{{/blocks}}
{{#outputs}}
         ({{name}} {{input}})
{{/outputs}}
        )
    (list{{#outputs}} {{name}}{{/outputs}})))
