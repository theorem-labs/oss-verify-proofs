set -e










: "${SOURCE_DATE_EPOCH:=1756684800}"
export SOURCE_DATE_EPOCH










LR_STAMP=/tmp/oft-link-record.started
: > "$LR_STAMP"
sleep 1

CHOST=riscv64-linux-musl





























OFT_NO_BUILTIN_ALLOC="-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-reallocarray -fno-builtin-free -fno-builtin-aligned_alloc -fno-builtin-posix_memalign -fno-builtin-memalign -fno-builtin-valloc -fno-builtin-strdup -fno-builtin-strndup"
BASE_CFLAGS="-march=rv64g -mabi=lp64d -Os -g -ffunction-sections -fdata-sections -fno-stack-protector -fno-plt -Wdate-time $OFT_NO_BUILTIN_ALLOC"

if [ "$FLAV" = gcc ]; then
  CC=$CHOST-gcc
  CXX=$CHOST-g++
  DRVCC=$CC
  SAN=""
else






  SHIM=/tmp/shim; mkdir -p "$SHIM"; PATH=$SHIM:$PATH; export PATH


























  OFT_SYSROOT_FLAG=""
  if [ "${OFT_MUSL_PATCHED:-0}" = 1 ]; then
    [ "$FLAV" != gcc ] || { echo "musl-from-materials is not wired for the gcc flavour" >&2; exit 1; }
    [ -f /work/musl/configure ] && [ -d /work/musl/src/env ] \
      || { echo "OFT_MUSL_PATCHED=1 but /work/musl is not a musl source tree" >&2; exit 1; }
    MUSL_TRIPLE=$(cat /opt/target-pkgs/alpine-triple)
    MUSL_BUILD=/tmp/musl-build; MUSL_INST=/tmp/musl-inst; MUSL_OVL=/tmp/musl-sysroot
    rm -rf "${MUSL_BUILD:?}" "${MUSL_INST:?}" "${MUSL_OVL:?}"
    mkdir -p "$MUSL_BUILD" "$MUSL_INST"
    echo "==> musl-from-materials: OFT_MUSL_PATCHED=1, building /work/musl" >&2
    musl_t0=$(date +%s)
    if ! ( cd "$MUSL_BUILD" \
        && /work/musl/configure --target=riscv64-linux-musl --prefix=/usr --exec-prefix=/usr \
             --syslibdir=/usr/lib --disable-gcc-wrapper \
             CC="clang --target=$MUSL_TRIPLE -fuse-ld=lld" AR=llvm-ar RANLIB=llvm-ranlib \
             CFLAGS="-march=rv64g -mabi=lp64d -ffunction-sections -fdata-sections" \
             >/tmp/musl-configure.log 2>&1 \
        && make -j"$(nproc)" >/tmp/musl-make.log 2>&1 \
        && make DESTDIR="$MUSL_INST" install >>/tmp/musl-make.log 2>&1 ); then
      echo "musl-from-materials: the musl build FAILED; last lines:" >&2
      tail -40 /tmp/musl-configure.log /tmp/musl-make.log >&2
      exit 1
    fi
    [ -f "$MUSL_INST/usr/lib/libc.a" ] && [ -f "$MUSL_INST/usr/lib/crt1.o" ] \
      || { echo "musl-from-materials: install produced no usr/lib/libc.a + crt1.o" >&2; exit 1; }






    mkdir -p "$MUSL_OVL/usr"
    for e in /opt/musl-sysroot/usr/* /opt/musl-sysroot/usr/.[!.]*; do
      [ -e "$e" ] || [ -L "$e" ] || continue
      case "${e##*/}" in lib|include) ;; *) ln -s "$e" "$MUSL_OVL/usr/${e##*/}" ;; esac
    done
    for sub in lib include; do
      mkdir -p "$MUSL_OVL/usr/$sub"
      ( cd "$MUSL_INST/usr/$sub" && cp -a . "$MUSL_OVL/usr/$sub/" )
      ( cd "$MUSL_OVL/usr/$sub" && find . -type d ) | while IFS= read -r d; do
        for e in "/opt/musl-sysroot/usr/$sub/$d"/* "/opt/musl-sysroot/usr/$sub/$d"/.[!.]*; do
          [ -e "$e" ] || [ -L "$e" ] || continue
          n=${e##*/}
          [ -e "$MUSL_OVL/usr/$sub/$d/$n" ] || [ -L "$MUSL_OVL/usr/$sub/$d/$n" ] \
            || ln -s "$e" "$MUSL_OVL/usr/$sub/$d/$n"
        done
      done
    done
    [ -f "$MUSL_OVL/usr/lib/libc.a" ] && [ ! -L "$MUSL_OVL/usr/lib/libc.a" ] \
      && [ -e "$MUSL_OVL/usr/lib/libc++.a" ] && [ -e "$MUSL_OVL/usr/include/linux/version.h" ] \
      || { echo "musl-from-materials: overlay is incomplete (libc.a real, libc++.a and linux/version.h reachable)" >&2; exit 1; }
    OFT_SYSROOT_FLAG=" --sysroot=$MUSL_OVL"



    OFT_SYSROOT=$MUSL_OVL; MUSL_SYSROOT=$MUSL_OVL; PKG_CONFIG_LIBDIR=$MUSL_OVL/usr/lib/pkgconfig
    export OFT_SYSROOT MUSL_SYSROOT PKG_CONFIG_LIBDIR
    echo "==> musl-from-materials: libc built from /work/musl and overlaid at $MUSL_OVL in $(( $(date +%s) - musl_t0 )) s" >&2
  fi
  for tool in ar nm ranlib strip objdump objcopy readelf size; do
    printf '#!/bin/sh\nexec llvm-%s "$@"\n' "$tool" > "$SHIM/$CHOST-$tool"
    chmod +x "$SHIM/$CHOST-$tool"
  done




















  OFT_ARCH_PIN='n=$#; i=0
while [ "$i" -lt "$n" ]; do
  a=$1; shift
  case "$a" in -march=rv*) a=-march=rv64g ;; esac
  set -- "$@" "$a"
  i=$((i+1))
done'


















  mkdir -p "$SHIM/include/asm"
  cat > "$SHIM/include/riscv_vector.h" <<'POISON'
                                                                       
                                                                     
                                                                            
#if !defined(__riscv_vector)
#error "riscv_vector.h: this toolchain pins -march=rv64g; the vector extension is unavailable"
#endif
#include_next <riscv_vector.h>
POISON















  cat > "$SHIM/include/asm/hwprobe.h" <<'POISON'
                                                                        
                                                                          
                                                                  
                                                   
#error "asm/hwprobe.h: riscv_hwprobe is not part of the modeled platform; use getauxval(AT_HWCAP)"
POISON

























  OFT_REL_FLAGS=""
  OFT_REL_CASES=""
  if [ "${OFT_RELEASE:-0}" = 1 ]; then
    [ ! -e /src ] || { echo "oft release: /src already exists in this image; the neutral source layout needs it" >&2; exit 1; }


    rel_pair() {
      mkdir -p "$(dirname "${2%/}")" && ln -s "${1%/}" "${2%/}" || exit 1
      OFT_REL_CASES="$OFT_REL_CASES      \"$1\"*) a=\"$2\${a#\"$1\"}\" ;;
"
      OFT_REL_FLAGS="$OFT_REL_FLAGS -fmacro-prefix-map=$1=$2 -fdebug-prefix-map=$2=$1"
    }









    rel_pair_spelled() {
      rs_d="/work/build/release-spell/$FLAV/$T/$1"
      mkdir -p /src/harness && ln -s "/work/targets/$1" "/src/harness/$1" || exit 1
      rs_arms=$(awk -F '\t' 'NF == 2 { print length($1) "\t" $1 "\t" $2 }' "$rs_d/renames.tsv" | sort -rn | cut -f2-) || exit 1
      while IFS="$(printf '\t')" read -r rs_o rs_n; do
        [ -n "$rs_o" ] || continue
        case "$rs_o" in
          */) OFT_REL_CASES="$OFT_REL_CASES      \"/work/targets/$1/$rs_o\"*) oft_rp_o=\"$rs_d/orig/\${a#\"/work/targets/$1/\"}\"; a=\"/src/harness/$1/$rs_n\${a#\"/work/targets/$1/$rs_o\"}\"; oft_rel_pp=\"\$oft_rel_pp \$a=\$oft_rp_o\" ;;
" ;;
          *)  OFT_REL_CASES="$OFT_REL_CASES      \"/work/targets/$1/$rs_o\") oft_rp_o=\"$rs_d/orig/$rs_o\"; a=\"/src/harness/$1/$rs_n\"; oft_rel_pp=\"\$oft_rel_pp \$a=\$oft_rp_o\" ;;
" ;;
        esac
        OFT_REL_FLAGS="$OFT_REL_FLAGS -fmacro-prefix-map=/work/targets/$1/$rs_o=/src/harness/$1/$rs_n -fmacro-prefix-map=/src/harness/$1/$rs_o=/src/harness/$1/$rs_n"
      done <<RSARMS
$rs_arms
RSARMS
      OFT_REL_CASES="$OFT_REL_CASES      \"/work/targets/$1/\"*) oft_rp_o=\"$rs_d/orig/\${a#\"/work/targets/$1/\"}\"; a=\"/src/harness/$1/\${a#\"/work/targets/$1/\"}\"; oft_rel_pp=\"\$oft_rel_pp \$a=\$oft_rp_o\" ;;
"
      OFT_REL_FLAGS="$OFT_REL_FLAGS -fmacro-prefix-map=/work/targets/$1/=/src/harness/$1/ -fdebug-prefix-map=/src/harness/$1/=/work/targets/$1/"
      OFT_REL_PP_SPELL="/work/build/release-spell/$FLAV/$T"
    }






    rel_pair_libcopy() {
      mkdir -p "$(dirname "/src/$1")" && ln -s "/work/$LIBREL/$1" "/src/$1" || exit 1
      OFT_REL_CASES="$OFT_REL_CASES      \"/work/$LIBREL/$1/src/\"*) a=\"/src/$1/\${a#\"/work/$LIBREL/$1/\"}\" ;;
      \"/work/$LIBREL/$1/\"*[Aa][Ee][Ff]*) a=\$(oft_rel_ours \"/work/$LIBREL/$1/\" \"/src/$1/\" \"\$a\") || exit 1 ;;
      \"/work/$LIBREL/$1/\"*) a=\"/src/$1/\${a#\"/work/$LIBREL/$1/\"}\" ;;
"
      OFT_REL_FLAGS="$OFT_REL_FLAGS -fmacro-prefix-map=/work/$LIBREL/$1/=/src/$1/ -fdebug-prefix-map=/src/$1/=/work/$LIBREL/$1/"
    }
    OFT_REL_PP_SPELL=""
    OFT_REL_PP_LOG="/work/$OBJREL/$T/release-ppcheck.log"
    rel_seen=" "
    for N in ${DEPS:-} $T; do
      case "$rel_seen" in *" $N "*) continue ;; esac
      rel_seen="$rel_seen$N "
      case "$N" in vendor|ext|ext-vendor|harness|driver|repo)
        echo "oft release: target name $N collides with the neutral layout under /src" >&2; exit 1 ;; esac
      rel_pair "/work/$LIBREL/$N/src/oft-vendor/" "/src/vendor/$N/"
      rel_pair "/work/ext/$N/src/oft-vendor/" "/src/ext-vendor/$N/"
      rel_pair_libcopy "$N"
      rel_pair "/work/ext/$N/" "/src/ext/$N/"
      if [ -d "/work/build/release-spell/$FLAV/$T/$N/orig" ]; then rel_pair_spelled "$N"
      else rel_pair "/work/targets/$N/" "/src/harness/$N/"; fi
    done
    rel_pair /work/src/ /src/driver/
    rel_pair /work/ /src/repo/



    OFT_REL_FLAGS="$OFT_REL_FLAGS -fmacro-prefix-map=oft-vendor/=vendor/"

    if [ -f "/work/build/release-spell/$FLAV/$T/CONTROL-UNSPELLED" ]; then
      echo "==> oft release: CONTROL build without the release spelling (no OFT_RELEASE_BUILD); never shipped" >&2
    else
      OFT_REL_FLAGS="$OFT_REL_FLAGS -DOFT_RELEASE_BUILD=1"
    fi
    OFT_ARCH_PIN='n=$#; i=0
while [ "$i" -lt "$n" ]; do
  a=$1; shift
  case "$a" in -march=rv*) a=-march=rv64g ;; esac
  case "$a" in
    *.c|*.cc|*.cpp|*.cxx|*.c++|*.C|*.cp|*.CPP|*.m|*.mm|*.S|*.s|*.sx|*.i|*.ii)
      if [ -f "$a" ]; then
        case "$a" in /*) ;; *oft-vendor*) a="$PWD/$a" ;; esac
        case "$a" in
'"$OFT_REL_CASES"'        esac
      fi ;;
  esac
  set -- "$@" "$a"
  i=$((i+1))
done'




    OFT_ARCH_PIN='oft_rel_ours() {
  ro_b=${1%/}; ro_s=${3#"$1"}; ro_o=
  while [ -n "$ro_s" ]; do
    ro_c=${ro_s%%/*}
    if [ "$ro_c" = "$ro_s" ]; then ro_s=; else ro_s=${ro_s#*/}; fi
    ro_n=$(printf "%s\n" "$ro_c" | awk "BEGIN { split(\"97 101 102 65 69 70 65 101 102\", i, \" \"); split(\"111 102 116 79 70 84 79 102 116\", r, \" \"); for (k = 0; k < 3; k++) { f[k] = sprintf(\"%c%c%c\", i[3*k+1], i[3*k+2], i[3*k+3]); t[k] = sprintf(\"%c%c%c\", r[3*k+1], r[3*k+2], r[3*k+3]) } } { for (k = 0; k < 3; k++) gsub(f[k], t[k]); print }")
    if [ "$ro_n" != "$ro_c" ]; then
      [ -L "$ro_b/$ro_n" ] || [ -e "$ro_b/$ro_n" ] || ln -s "$ro_c" "$ro_b/$ro_n" 2>/dev/null || [ -L "$ro_b/$ro_n" ] || return 1
      [ "$(readlink "$ro_b/$ro_n")" = "$ro_c" ] || { echo "oft release: $ro_b/$ro_n is taken; cannot spell $ro_c" >&2; return 1; }
    fi
    ro_b="$ro_b/$ro_n"; ro_o="$ro_o${ro_o:+/}$ro_n"
  done
  printf "%s%s\n" "$2" "$ro_o"
}
'"$OFT_ARCH_PIN"

    if [ -n "$OFT_REL_PP_SPELL" ]; then
      OFT_ARCH_PIN="oft_rel_pp=
$OFT_ARCH_PIN"
      : > "$OFT_REL_PP_LOG"
    fi
    echo "==> oft release: neutral source layout under /src; install prefix /opt/oft/<t>; $(printf '%s' "$OFT_REL_CASES" | grep -c 'a=') path rewrites" >&2
  fi























  oft_write_cc_shim() {
    { printf '#!/bin/sh\n%s\n' "$OFT_ARCH_PIN"



      printf 'nogc="-Wl,--no-gc-sections%s"; for a in "$@"; do case "$a" in -c|-E|-S|-fsyntax-only|-M|-MM|--version|-dumpmachine|-print-*) nogc=;; esac; done\n' "${3:-}"




      if [ -n "${OFT_REL_PP_SPELL:-}" ]; then
        printf '[ -z "$oft_rel_pp" ] || python3 -B %s/tools/rel_text.py ppcheck --spell %s --log %s $oft_rel_pp -- %s%s%s -isystem %s/include "$@" || exit 1\n' \
          "$OFT_REL_PP_SPELL" "$OFT_REL_PP_SPELL" "$OFT_REL_PP_LOG" "$2" "$OFT_SYSROOT_FLAG" "$OFT_REL_FLAGS" "$SHIM"
      fi
      printf 'exec ${OFT_CC_PREFIX:-} %s%s%s $nogc -isystem %s/include "$@"\n' "$2" "$OFT_SYSROOT_FLAG" "$OFT_REL_FLAGS" "$SHIM"
    } > "$1"
  }
  oft_write_cc_shim "$SHIM/$CHOST-clang-plain" \
    'clang --config=/opt/asan-static/musl.cfg'








  oft_write_cc_shim "$SHIM/$CHOST-clang++-plain" \
    'clang++ --config=/opt/asan-static/musl.cfg -stdlib=libc++'




































  SEALED_CFG=/opt/asan-static/asan-musl-sealed.cfg
  WRAP_SRC=$(sed -n 's/^-Wl,@//p' "$SEALED_CFG")
  if [ -z "$WRAP_SRC" ] || [ ! -f "$WRAP_SRC" ]; then
    echo "build.sh: no -Wl,@<wrap list> in $SEALED_CFG (got '${WRAP_SRC:-}')" >&2
    echo "  The sealed config's shape changed; re-derive the iconv filter." >&2
    exit 1
  fi
  if ! grep -qx -- '--wrap=iconv' "$WRAP_SRC"; then
    echo "build.sh: no '--wrap=iconv' in $WRAP_SRC" >&2
    echo "  The runtime no longer intercepts iconv, so this filter is dead." >&2
    echo "  Drop it (and the 143 KB is already gone) rather than leaving it." >&2
    exit 1
  fi
  grep -vx -- '--wrap=iconv' "$WRAP_SRC" > /tmp/asan-noiconv.wrap
  sed 's|^-Wl,@.*|-Wl,@/tmp/asan-noiconv.wrap|' "$SEALED_CFG" > /tmp/asan-musl-sealed-noiconv.cfg















































  printf 'SECTIONS { /DISCARD/ : { *(.data.rel.ro.__interception_extract_*) } } INSERT AFTER .text;\n' \
    > "$SHIM/oft-nogc-discard.ld"
  oft_write_cc_shim "$SHIM/$CHOST-clang-sealed" \
    'clang --config=/tmp/asan-musl-sealed-noiconv.cfg' " $SHIM/oft-nogc-discard.ld"
  oft_write_cc_shim "$SHIM/$CHOST-clang++-sealed" \
    'clang++ --config=/tmp/asan-musl-sealed-noiconv.cfg -stdlib=libc++' " $SHIM/oft-nogc-discard.ld"
  chmod +x "$SHIM/$CHOST-clang-plain" "$SHIM/$CHOST-clang-sealed" \
           "$SHIM/$CHOST-clang++-plain" "$SHIM/$CHOST-clang++-sealed"
  DRVCC=$SHIM/$CHOST-clang-plain
  DRVCXX=$SHIM/$CHOST-clang++-plain
  if [ "$FLAV" = asan ]; then
    CC=$SHIM/$CHOST-clang-sealed
    CXX=$SHIM/$CHOST-clang++-sealed







    SAN="-fsanitize=address"
  elif [ "$FLAV" = asanubsan ]; then













    CC=$SHIM/$CHOST-clang-sealed
    CXX=$SHIM/$CHOST-clang++-sealed
    SAN="-fsanitize=address -fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
  elif [ "$FLAV" = ubsan ]; then





    CC=$DRVCC
    CXX=$DRVCXX
    SAN="-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
  else
    CC=$DRVCC
    CXX=$DRVCXX
    SAN=""
  fi
fi


LIBROOT=/work/$LIBREL






















CFLAGS="$BASE_CFLAGS $SAN -fmacro-prefix-map=$LIBROOT/=/work/build/lib/FLAVOUR/"



if [ "${OFT_RELEASE:-0}" = 1 ]; then CFLAGS="$BASE_CFLAGS $SAN"; fi












export LIBROOT CHOST CC CXX CFLAGS DRVCC DRVCXX BASE_CFLAGS





















oft_link_prefix() {
  local name="${1:?}" link
  link="/oft/$name"

  if [ "${OFT_RELEASE:-0}" = 1 ]; then link="/opt/oft/$name"; fi
  mkdir -p "$(dirname "$link")"
  if [ -L "$link" ]; then
    [ "$(readlink "$link")" = "$BUILDDIR" ] || { echo "oft: $link points at $(readlink "$link"), not $BUILDDIR" >&2; return 1; }
  else
    [ ! -e "$link" ] || { echo "oft: $link exists and is not a symlink" >&2; return 1; }
    ln -s "$BUILDDIR" "$link" || return 1
  fi
  OFT_PREFIX="$link"; export OFT_PREFIX
}






for D in ${DEPS:-}; do

  ( SRCDIR=/work/ext/$D/src
    BUILDDIR=$LIBROOT/$D
    export SRCDIR BUILDDIR
    mkdir -p "$BUILDDIR"
    oft_link_prefix "$D" || exit 1
    . /work/targets/$D/pin
    if [ -f /work/harness/native/overrides/$D.sh ]; then . /work/harness/native/overrides/$D.sh
    elif [ -f /work/targets/$D/override.sh ]; then . /work/targets/$D/override.sh; fi
    build_lib )
done

SRCDIR=/work/$SRCREL
BUILDDIR=$LIBROOT/$T
export SRCDIR BUILDDIR
mkdir -p "$BUILDDIR"
oft_link_prefix "$T" || exit 1














trap 'rc=$?; if [ "$rc" -ne 0 ]; then for d in "$BUILDDIR" $(for D in ${DEPS:-}; do echo "$LIBROOT/$D"; done); do f="$d/partial-build"; [ -f "$f" ] || continue; echo "oft: NOTE -- this failure came AFTER a keep-going retry in $d; the first error of that pass, below, is the likely cause:" >&2; cat "$f" >&2; done; fi; [ "${LR_PENDING:-0}" = 0 ] || lr_on_exit "$rc"' EXIT


. /work/targets/$T/pin












if [ -f /work/harness/native/overrides/$T.sh ]; then . /work/harness/native/overrides/$T.sh
elif [ -f /work/targets/$T/override.sh ]; then . /work/targets/$T/override.sh; fi
build_lib



















if [ -n "${LIB_ARCHIVE:-}" ]; then
  if command -v oft_stub_gate >/dev/null 2>&1; then



    oft_single_entry "$BUILDDIR/$LIB_ARCHIVE" || exit 1
    oft_stub_gate "$BUILDDIR/$LIB_ARCHIVE" "$BUILDDIR/harness.o" || exit 1
  else
    echo "oft: stub gate SKIPPED for $T -- its pin does not source recipes.sh," \
         "so oft_stub_gate is undefined here (hand-written pin)" >&2
  fi
fi

LINK=""
if [ -n "${LIB_ARCHIVE:-}" ]; then LINK="$BUILDDIR/$LIB_ARCHIVE"; fi


LINK="$LINK ${LIB_EXTRA:-}"

OBJ=/work/$OBJREL
mkdir -p "$OBJ/$T"




































LR_REC="$OBJ/$T/link-record.tsv"
LR_IN="$OBJ/$T/link-record.inputs"
LR_SIDE="$OBJ/$T/link-record.side"
: > "$LR_IN"; : > "$LR_SIDE"; LR_PENDING=0
if [ "$FLAV" = gcc ]; then
  LR_MAP=""; LR_MAPFLAG=""
else
  LR_MAP=/tmp/oft-link-record.map; LR_MAPFLAG="-Wl,-Map=$LR_MAP"
  : > "$LR_MAP"
fi



























lr_reduce() {
  [ -n "$LR_MAP" ] || return 0
  [ -s "$LR_MAP" ] || { echo "build.sh: link record: the link of $2 wrote no map ($LR_MAP)" >&2; exit 1; }
  awk -v L="$1" -v O="${2##*/}" '
    match($0, /^ *[0-9a-f]+ +[0-9a-f]+ +[0-9a-f]+ +[0-9]+ /) {
      rest = substr($0, RLENGTH + 1)
      if (substr(rest, 1, 8) != "        " || substr(rest, 9, 1) == " " || substr(rest, 9, 1) == "") next
      e = substr(rest, 9)
      if (!match(e, /:\([^()]*\)$/)) next
      f = substr(e, 1, RSTART - 1)
      if (f == "<internal>") next
      match(f, /[^\/]*$/); d = substr(f, 1, RSTART - 1); b = substr(f, RSTART)
      p = O ".lto."
      if (O != "" && substr(b, 1, length(p)) == p && match(b, / at [0-9]+\)\.o$/)) {
        a = substr(b, length(p) + 1, RSTART - length(p) - 1)
        k = index(a, "(")
        if (k > 3 && substr(a, k - 2, 2) == ".a" && k < length(a)) {
          print L "\t" d substr(a, 1, k - 1) "\t" substr(a, k + 1); next
        }
      }
      if (match(f, /\.a\(.*\)$/)) { print L "\t" substr(f, 1, RSTART + 1) "\t" substr(f, RSTART + 3, RLENGTH - 4) }
      else print L "\t" f "\t-"
    }' "$LR_MAP" > "$LR_MAP.in" || { echo "build.sh: link record: cannot read the map of $2" >&2; exit 1; }
  [ -s "$LR_MAP.in" ] || { echo "build.sh: link record: the map of $2 names no input section (examined nothing)" >&2; exit 1; }
  lr_o=$(sha256sum "/work/$2" | cut -d' ' -f1)
  [ "${#lr_o}" -eq 64 ] || { echo "build.sh: link record: no sha256 for the output /work/$2" >&2; exit 1; }
  sort -u "$LR_MAP.in" >> "$LR_IN" || exit 1
  printf 'link\t%s\t%s\t%s\n' "$1" "$2" "$lr_o" >> "$LR_SIDE"
  LR_PENDING=1
  : > "$LR_MAP"
}



lr_write() {
  [ -n "$LR_MAP" ] || return 0
  LR_PENDING=0


  lr_t0=$(stat -c %Z "$LR_STAMP" 2>/dev/null) && [ -n "$lr_t0" ] \
    || { echo "build.sh: link record: the build's start stamp $LR_STAMP is gone; origins cannot be told" >&2; exit 1; }
  LR_STORE=/work/build/linked-inputs
  mkdir -p "$LR_STORE"
  awk 'BEGIN { FS = "\t" }
       { k = $2
         if (!((k, $1) in L)) { L[k, $1] = 1; if (k in links) links[k] = links[k] "," $1; else links[k] = $1 }
         if ($3 != "-" && !((k, $3) in M)) { M[k, $3] = 1; n[k]++ }
         if (!(k in seen)) { seen[k] = 1; order[++no] = k } }
       END { for (i = 1; i <= no; i++) { k = order[i]; print k "\t" links[k] "\t" ((k in n) ? n[k] : 0) } }' \
      "$LR_IN" > "$LR_REC.byfile" || exit 1
  {
    printf 'oft-link-record\t1\n'
    printf 'target\t%s\nflavour\t%s\nlibroot\t%s\n' "$T" "$FLAV" "$LIBROOT"
    cat "$LR_SIDE"
    for lr_t in $LINK; do printf 'token\t%s\n' "$lr_t"; done




    while IFS="$(printf '\t')" read -r lr_p lr_l lr_n; do
      lr_r=$(readlink -f "$lr_p") && [ -f "$lr_r" ] \
        || { case "$lr_p" in
               *.lto.*) echo "build.sh: link record: input $lr_p (named by the map) is not a file: an object lld compiled from bitcode, in a form other than an archive member's (lr_reduce's header), so the bitcode it came from cannot be told" >&2 ;;
               *) echo "build.sh: link record: input $lr_p (named by the map) is not a file" >&2 ;;
             esac; exit 1; }
      lr_s=$(sha256sum "$lr_r" | cut -d' ' -f1)
      [ "${#lr_s}" -eq 64 ] || { echo "build.sh: link record: no sha256 for $lr_r" >&2; exit 1; }
      lr_z=$(wc -c < "$lr_r" | tr -d ' ')
      case "$lr_p" in *.a) lr_k=archive ;; *) lr_k=object ;; esac
      lr_st=-; lr_or=work
      case "$lr_r" in
        /work/*) ;;
        *) lr_c=$(stat -c %Z "$lr_r") || exit 1
           if [ "$lr_c" -gt "$lr_t0" ]; then lr_or=build; else lr_or=image; fi






           if [ ! -f "$LR_STORE/$lr_s" ]; then
             lr_d=$(mktemp -d "$LR_STORE/.store.XXXXXX") && cp -- "$lr_r" "$lr_d/$lr_s" \
               && mv -f -- "$lr_d/$lr_s" "$LR_STORE/$lr_s" && rmdir -- "$lr_d" \
               || { echo "build.sh: link record: cannot store $lr_r" >&2; exit 1; }
           fi
           lr_st=build/linked-inputs/$lr_s ;;
      esac
      printf 'input\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$lr_p" "$lr_r" "$lr_s" "$lr_z" "$lr_k" "$lr_l" "$lr_n" "$lr_st" "$lr_or"
    done < "$LR_REC.byfile"
  } > "$LR_REC.new" || { echo "build.sh: link record: could not be written" >&2; exit 1; }
  mv -f -- "$LR_REC.new" "$LR_REC"
  echo "oft: link record: $(grep -c '^input' "$LR_REC") input file(s) over $(grep -c '^link' "$LR_REC") link(s) -> $LR_REC"
}














lr_on_exit() {
  [ "${LR_PENDING:-0}" = 1 ] || return 0
  echo "build.sh: link record: the body is exiting with status $1 after links not yet recorded; writing the record of the links that completed" >&2
  ( lr_write ) || echo "build.sh: link record: the record of the links that completed could not be written (above)" >&2
}



if [ -n "${LIB_ARCHIVE:-}" ]; then PLUGCC=$DRVCC; PLUGFLAGS=$BASE_CFLAGS
else                               PLUGCC=$CC;    PLUGFLAGS=$CFLAGS; fi






"$DRVCC" $BASE_CFLAGS -c -I/work/src /work/src/cli.c -o "$OBJ/$T/cli.o"

"$DRVCC" $BASE_CFLAGS -DHARNESS_QUIET -c -I/work/src /work/src/cli.c -o "$OBJ/$T/cli-quiet.o"






cat /work/src/cli.c /work/src/grow_buf.h /work/src/target.h | sha256sum | awk '{print $1}' > "$OBJ/$T/cli.o.src-sha"
cp "$OBJ/$T/cli.o.src-sha" "$OBJ/$T/cli-quiet.o.src-sha"


"$PLUGCC" $PLUGFLAGS -c -I/work/src -I"$SRCDIR" ${LIB_CFLAGS:-} \
    /work/targets/$T/plugin.c -o "$OBJ/$T/plugin.o"





"$PLUGCC" $PLUGFLAGS -DHARNESS_QUIET -c -I/work/src -I"$SRCDIR" ${LIB_CFLAGS:-} \
    /work/targets/$T/plugin.c -o "$OBJ/$T/plugin-quiet.o"






















EXTRA_OBJ=""










SILENT_LD=""
if [ "$FLAV" = asan ] || [ "$FLAV" = asanubsan ]; then
  SILENT_LD="-Wl,--defsym=__sanitizer_silent_reports=1"
fi



if [ "${OFT_SILENT_CONTROL_BUILD:-0}" = 1 ] && [ -n "$SILENT_LD" ]; then
  SILENT_LD=""
  echo "WARNING: OFT_SILENT_CONTROL_BUILD=1 -- building the NO-DEFSYM control; do not ship this binary" >&2
fi



















"$CC" $BASE_CFLAGS -static -no-pie -Wl,--gc-sections ${OFT_STRIP--Wl,--strip-all} \
    "$OBJ/$T/cli.o" "$OBJ/$T/plugin.o" $EXTRA_OBJ $SILENT_LD $LINK $LR_MAPFLAG \
    -o /work/$OUTDIR/$NAME$SFX
lr_reduce harness "$OUTDIR/$NAME$SFX"

"$CC" $BASE_CFLAGS -static -no-pie -Wl,--gc-sections ${OFT_STRIP--Wl,--strip-all} \
    "$OBJ/$T/cli-quiet.o" "$OBJ/$T/plugin-quiet.o" $EXTRA_OBJ $SILENT_LD $LINK $LR_MAPFLAG \
    -o /work/$OUTDIR/$NAME$QSFX
lr_reduce harness-quiet "$OUTDIR/$NAME$QSFX"




























































































































































































































































































































































































































































































































































































































































































































































































































































































lr_write






if [ -n "${OFT_CC_PREFIX:-}" ]; then
  ccache --print-stats | awk -F'\t' '$1=="direct_cache_hit"||$1=="preprocessed_cache_hit"{h+=$2} $1=="cache_miss"{m+=$2} END{printf "CCACHE_STATS hits=%d misses=%d\n", h, m}'
fi
