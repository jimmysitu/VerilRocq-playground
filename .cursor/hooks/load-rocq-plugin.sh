#!/bin/bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
workspace_from_script="$(cd "${script_dir}/../.." && pwd)"
log_file="${workspace_from_script}/.cursor/hooks/load-rocq-plugin.log"
debug_log="/tmp/cursor-load-rocq-hook.log"

log() {
  local line="[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"
  printf '%s\n' "${line}" >> "${log_file}" 2>/dev/null || true
  printf '%s\n' "${line}" >> "${debug_log}" 2>/dev/null || true
}

log "hook invoked pid=$$ pwd=$(pwd) HOME=${HOME:-<empty>} CURSOR_PROJECT_DIR=${CURSOR_PROJECT_DIR:-<empty>}"

python3_bin="$(command -v python3 || true)"
rsync_bin="$(command -v rsync || true)"
cp_bin="$(command -v cp || true)"

input="$(cat 2>/dev/null || true)"
workspace_root=""

if [[ -n "${input}" && -n "${python3_bin}" ]]; then
  workspace_root="$("${python3_bin}" -c "
import json, sys
try:
    data = json.load(sys.stdin)
    roots = data.get('workspace_roots') or []
    if roots:
        print(roots[0])
except Exception:
    pass
" <<< "${input}" 2>/dev/null || true)"
fi

if [[ -z "${workspace_root}" && -n "${CURSOR_PROJECT_DIR:-}" ]]; then
  workspace_root="${CURSOR_PROJECT_DIR}"
fi

if [[ -z "${workspace_root}" && -f "${workspace_from_script}/rocq-skills/plugins/rocq/.cursor-plugin/plugin.json" ]]; then
  workspace_root="${workspace_from_script}"
fi

source_plugin="${workspace_root}/rocq-skills/plugins/rocq"
local_root="${HOME}/.cursor/plugins/local"
local_plugin="${local_root}/rocq"
manifest="${local_plugin}/.cursor-plugin/plugin.json"

log "resolved workspace_root=${workspace_root:-<empty>} source=${source_plugin} target=${local_plugin}"

if [[ -z "${workspace_root}" || ! -f "${source_plugin}/.cursor-plugin/plugin.json" ]]; then
  log "skip missing source=${source_plugin}"
  printf '{}\n'
  exit 0
fi

mkdir -p "${local_root}"
if [[ -L "${local_plugin}" || -e "${local_plugin}" ]]; then
  log "remove existing target at ${local_plugin}"
  rm -rf "${local_plugin}"
fi

sync_ok=0
if [[ -n "${rsync_bin}" ]]; then
  if "${rsync_bin}" -a "${source_plugin}/" "${local_plugin}/"; then
    sync_ok=1
    log "rsync ok"
  else
    log "rsync failed exit=$?"
  fi
fi

if [[ "${sync_ok}" -eq 0 && -n "${cp_bin}" ]]; then
  mkdir -p "${local_plugin}"
  if "${cp_bin}" -a "${source_plugin}/." "${local_plugin}/"; then
    sync_ok=1
    log "cp ok"
  else
    log "cp failed exit=$?"
  fi
fi

if [[ "${sync_ok}" -eq 1 && -f "${manifest}" ]]; then
  log "verify ok target=${local_plugin}"
  printf '{"pluginPaths":["%s"]}\n' "${local_plugin}"
else
  log "verify failed sync_ok=${sync_ok} manifest_exists=$([[ -f "${manifest}" ]] && echo yes || echo no)"
  printf '{}\n'
fi
