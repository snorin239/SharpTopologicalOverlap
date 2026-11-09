$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$probePath = Join-Path $PSScriptRoot 'BlockG.lean'
$probeText = Get-Content -LiteralPath $probePath -Raw
$exampleStart = $probeText.IndexOf('/-! Independent declaration')
$exampleEnd = $probeText.IndexOf('-- Axioms for all public theorem')
if ($exampleStart -lt 0 -or $exampleEnd -le $exampleStart) {
  throw 'Could not locate the preserved edge-case probes.'
}
$examples = $probeText.Substring($exampleStart, $exampleEnd - $exampleStart).TrimEnd()
$sources = @(
  Get-Item -LiteralPath (Join-Path $projectRoot 'SharpTopologicalOverlap/Intersection.lean')
  Get-ChildItem -LiteralPath (Join-Path $projectRoot 'SharpTopologicalOverlap/Geometry') -Filter '*.lean' -Recurse
  Get-ChildItem -LiteralPath (Join-Path $projectRoot 'SharpTopologicalOverlap/Intersection') -Filter '*.lean' -Recurse
) | Sort-Object FullName
$lines = [System.Collections.Generic.List[string]]::new()
$lines.Add('module')
$lines.Add('')
foreach ($source in $sources) {
  $relative = $source.FullName.Substring($projectRoot.Length + 1)
  $module = $relative.Substring(0, $relative.Length - 5).Replace('\', '.').Replace('/', '.')
  $lines.Add('import ' + $module)
}
$lines.Add('')
$lines.Add($examples)
$lines.Add('')
$lines.Add('-- Axioms for all public theorem declarations in the audited source modules.')
$declarationCount = 0
foreach ($source in $sources) {
  $relative = $source.FullName.Substring($projectRoot.Length + 1).Replace('\', '/')
  $lines.Add('')
  $lines.Add('-- ' + $relative)
  $scopes = [System.Collections.Generic.List[object]]::new()
  $commentDepth = 0
  foreach ($sourceLine in Get-Content -LiteralPath $source.FullName) {
    $openComments = [regex]::Matches($sourceLine, '/-').Count
    $closeComments = [regex]::Matches($sourceLine, '-/').Count
    if ($commentDepth -gt 0) {
      $commentDepth += $openComments - $closeComments
      continue
    }
    $commentStart = $sourceLine.IndexOf('/-')
    if ($commentStart -ge 0) {
      $commentDepth += $openComments - $closeComments
      $sourceLine = $sourceLine.Substring(0, $commentStart)
    }
    if ($sourceLine -cmatch '^namespace\s+([\w.]+)\s*$') {
      $scopes.Add(@{ Kind = 'namespace'; Name = $Matches[1] })
      continue
    }
    if ($sourceLine -cmatch '^(?:@\[[^\r\n]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$') {
      $scopes.Add(@{ Kind = 'section'; Name = $Matches[1] })
      continue
    }
    if ($sourceLine -cmatch '^end(?:\s+([\w.]+))?\s*$') {
      if ($scopes.Count -gt 0) { $scopes.RemoveAt($scopes.Count - 1) }
      continue
    }
    if ($sourceLine -cmatch '^(?:omit\b.*\bin\s+)?(?:@\[[^\r\n]*\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([\w.]+)') {
      $name = $Matches[1]
      if ($name.StartsWith('_root_.')) {
        $qualified = $name.Substring(7)
      } else {
        $namespaceParts = @($scopes | Where-Object { $_.Kind -eq 'namespace' } | ForEach-Object { $_.Name })
        $qualified = ($namespaceParts + $name) -join '.'
      }
      $lines.Add('#print axioms ' + $qualified)
      $declarationCount++
    }
  }
}
Set-Content -LiteralPath $probePath -Value $lines -Encoding utf8
[pscustomobject]@{ Modules = $sources.Count; PublicTheorems = $declarationCount; Probe = $probePath }
