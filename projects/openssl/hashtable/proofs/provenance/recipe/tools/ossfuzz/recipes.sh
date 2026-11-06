





































oft_require_target_cxx() {
  local inc="${OFT_CXX_INCLUDE:-/opt/musl-sysroot/usr/include/c++}"





















  local lib="${OFT_CXX_RUNTIME:-/opt/musl-sysroot/usr/lib/libc++.a}"
  lib=$(printf '%s\n' $lib | grep -m1 '\.a$')
  [ -n "$lib" ] || lib=/opt/musl-sysroot/usr/lib/libc++.a
  if [ -d "$inc" ] && [ -f "$lib" ]; then
    echo "oft: target C++ available (headers $inc, runtime $lib)"




















    local grp="$lib"
    local d
    for d in libc++abi.a libunwind.a; do
      [ -f "/opt/musl-sysroot/usr/lib/$d" ] && grp="$grp /opt/musl-sysroot/usr/lib/$d"
    done
    OFT_CXX_RUNTIME="-Wl,--start-group $grp -Wl,--end-group"
    return 0
  fi
  echo "oft: this image has no static C++ runtime for the target" >&2
  echo "     headers $inc: $([ -d "$inc" ] && echo present || echo MISSING)" >&2
  echo "     runtime $lib: $([ -f "$lib" ] && echo present || echo MISSING)" >&2
  echo "     Set OFT_CXX_INCLUDE and OFT_CXX_RUNTIME, or use an image carrying" >&2
  echo "     the RVC-clean libc++. This is a property of the IMAGE, not of this" >&2
  echo "     project: it blocks every C++ target at once and is fixed once." >&2
  return 1
}

















































oft_suppress_unused_arg_werror() {
  local f kept=""
  for f in $CFLAGS; do
    [ "$f" = "-fno-plt" ] || kept="$kept $f"
  done
  CFLAGS="${kept# }"
  case " $CFLAGS " in
    *" -Wno-unused-command-line-argument "*) ;;
    *) CFLAGS="$CFLAGS -Wno-unused-command-line-argument" ;;
  esac
  export CFLAGS
}


















oft_define_fuzzing_build_mode() {
  case " $CFLAGS " in
    *" -DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION "*) return 0 ;;
  esac
  CFLAGS="$CFLAGS -DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION"
  export CFLAGS
}



oft_copy_src() {
  oft_suppress_unused_arg_werror
  oft_define_fuzzing_build_mode
  rm -rf "$BUILDDIR/src"
  mkdir -p "$BUILDDIR/src"
  cp -a "$SRCDIR/." "$BUILDDIR/src/"
}



































































































oft_cxxlinkflags() {
  echo "-stdlib=libc++"
}































oft_cxx() {
  if [ -z "${CXX:-}" ]; then
    echo "oft: CXX is unset -- the C++ driver must be named, not derived from \$CC" >&2
    echo "  (\$CC is the C driver; it compiles C++ but links no C++ runtime)" >&2
    return 1
  fi
  echo "$CXX"
}














oft_cxxflags() {
  echo "$CFLAGS -stdlib=libc++"
}



















oft_cmake_toolchain() {
  local sysroot="${OFT_SYSROOT:-/opt/musl-sysroot}"
  cat > "$1" <<EOF
set(CMAKE_SYSTEM_NAME Linux)
set(CMAKE_SYSTEM_PROCESSOR riscv64)
set(CMAKE_SYSROOT "$sysroot")
set(CMAKE_FIND_ROOT_PATH "$sysroot" "$sysroot/usr")
set(CMAKE_C_COMPILER "$CC")
set(CMAKE_CXX_COMPILER "$(oft_cxx)")
set(CMAKE_C_FLAGS "$CFLAGS" CACHE STRING "" FORCE)
set(CMAKE_CXX_FLAGS "$(oft_cxxflags)" CACHE STRING "" FORCE)
set(CMAKE_EXE_LINKER_FLAGS "$(oft_cxxlinkflags)" CACHE STRING "" FORCE)
set(CMAKE_SHARED_LINKER_FLAGS "$(oft_cxxlinkflags)" CACHE STRING "" FORCE)
set(CMAKE_MODULE_LINKER_FLAGS "$(oft_cxxlinkflags)" CACHE STRING "" FORCE)
set(CMAKE_AR "/usr/bin/llvm-ar" CACHE FILEPATH "" FORCE)
set(CMAKE_RANLIB "/usr/bin/llvm-ranlib" CACHE FILEPATH "" FORCE)
set(CMAKE_NM "/usr/bin/llvm-nm" CACHE FILEPATH "" FORCE)
set(CMAKE_TRY_COMPILE_TARGET_TYPE EXECUTABLE)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
EOF
}














oft_keep_going_record() {
  local tool=$1 log=$2 mark="$BUILDDIR/partial-build" n= first=
  case "$tool" in
    ninja)
      n=$(grep -c '^FAILED: ' "$log" || true)


      first=$(awk '/^FAILED: /{p=1; c=0} p{print; c++} p && c>1 && (/^\[[0-9]+\/[0-9]+\] / || /^ninja: / || c>=60){exit}' "$log")
      ;;
    make)
      n=$(grep -c -E '^make(\[[0-9]+\])?: \*\*\* .*Error' "$log" || true)


      first=$(awk '{buf[NR%40]=$0} /^make(\[[0-9]+\])?: \*\*\* .*Error/{for(i=NR-39;i<=NR;i++) if(i>0) print buf[i%40]; exit}' "$log")
      ;;
    *) echo "oft_keep_going_record: unknown tool $tool" >&2; return 1 ;;
  esac
  {
    echo "$tool default target failed and was retried keep-going: ${n:-0} failed step(s) in that pass"
    echo "full keep-going log: $log"
    if [ -n "$first" ]; then echo "first failure:"; printf '%s\n' "$first"; fi
  } > "$mark"
  echo "oft: keep-going pass finished with ${n:-0} failed step(s); the FIRST failure was:" >&2
  if [ -n "$first" ]; then printf '%s\n' "$first" >&2; else echo "  (no failure block recognised in $log)" >&2; fi
  return 0
}



































oft_jobs() {
  if [ -n "${OFT_MAKE_JOBS:-}" ]; then echo "$OFT_MAKE_JOBS"; return 0; fi
  n=$(nproc)
  for f in /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory/memory.limit_in_bytes; do
    if [ -r "$f" ]; then
      lim=$(cat "$f")
      case "$lim" in
        ''|max|*[!0-9]*) ;;
        *) cap=$((lim / 1610612736)); [ "$cap" -ge 1 ] || cap=1; [ "$cap" -lt "$n" ] && n=$cap ;;
      esac
      break
    fi
  done
  echo "$n"
}

oft_make_then_keep_going() {
  rm -f "$BUILDDIR/partial-build"
  make -j"$(oft_jobs)" "$@" && return 0
  echo "oft: default target failed; retrying with make -k (see partial-build marker)" >&2
  echo "make failed, retried with -k" > "$BUILDDIR/partial-build"

















  make -k -j"$(oft_jobs)" "$@" 2>&1 | tee "$BUILDDIR/keep-going.log" || true
  oft_keep_going_record make "$BUILDDIR/keep-going.log"
  return 0
}
















































































oft_build_cmake() {
  oft_copy_src
  oft_cmake_toolchain "$BUILDDIR/toolchain.cmake"














  rm -rf "$BUILDDIR/cmk"
  mkdir -p "$BUILDDIR/cmk"



  local csub="$BUILDDIR/src"
  if [ -n "${OFT_CMAKE_SUBDIR:-}" ]; then csub="$csub/$OFT_CMAKE_SUBDIR"
  elif [ -n "${OFT_BUILD_SUBDIR:-}" ]; then csub="$csub/$OFT_BUILD_SUBDIR"; fi
  [ -d "$csub" ] || { echo "oft: cmake source dir $csub does not exist" >&2; return 1; }






  ( cd "$BUILDDIR/cmk" \
    && cmake "$csub" \
         -DCMAKE_TOOLCHAIN_FILE="$BUILDDIR/toolchain.cmake" \
         -DCMAKE_BUILD_TYPE=Release \
         -DCMAKE_INSTALL_PREFIX="${OFT_PREFIX:?build.sh sets the flavour-independent install prefix; see oft_link_prefix}" \
         -DBUILD_SHARED_LIBS=OFF \
         -DBUILD_TESTING=OFF -DBUILD_TESTS=OFF -DBUILD_EXAMPLES=OFF \
         -DBUILD_TOOLS=OFF -DENABLE_TESTS=OFF -DENABLE_EXAMPLES=OFF \
         -DSPIRV_SKIP_TESTS=ON \
         "$@" \
    && oft_make_then_keep_going )
  oft_merge_archives
}














































oft_build_header_only() {
  oft_copy_src
  mkdir -p "$BUILDDIR/lib"
  rm -f "$BUILDDIR/lib/liboft.a"


  local stub="$BUILDDIR/header-only-stub.c" obj="$BUILDDIR/header-only-stub.o"
  echo 'const char oft_header_only_marker = 0;' > "$stub"

  "$CC" $CFLAGS -c "$stub" -o "$obj" || return 1
  "$CHOST-ar" crs "$BUILDDIR/lib/liboft.a" "$obj" || return 1
  echo "oft: header-only recipe: the library is its headers; the harness TU carries it"
  LIB_ARCHIVE="lib/liboft.a"
}





























































oft_drop_redundant_archives() {
  local list=$1 d="$BUILDDIR/merge-syms" a n keep="$BUILDDIR/merge-keep.txt"
  [ -s "$list" ] || return 0
  rm -rf "$d"; mkdir -p "$d"

  n=0
  while IFS= read -r a; do
    n=$((n + 1))
    "$CHOST-nm" --defined-only "$a" 2>/dev/null \
      | awk 'NF>=2 && $(NF-1) ~ /^[TDBR]$/ {print $NF}' | sort -u > "$d/$n.sym"
    printf '%s\t%s\t%s\n' "$(wc -l < "$d/$n.sym")" "$n" "$a" >> "$d/index"
  done < "$list"
  [ -s "$d/index" ] || return 0
  : > "$d/kept.sym"; : > "$keep"
  local cnt idx dropped=0

  sort -rn "$d/index" | while IFS="$(printf '\t')" read -r cnt idx a; do
    if [ "${cnt:-0}" -eq 0 ]; then


      echo "$a" >> "$keep"; continue
    fi
    if [ -s "$d/kept.sym" ] && [ -z "$(comm -23 "$d/$idx.sym" "$d/kept.sym" | head -1)" ]; then
      echo "oft: merge: dropping $(basename "$a") -- every strong symbol it defines is already provided" >&2
      echo x >> "$d/dropped"
      continue
    fi
    echo "$a" >> "$keep"
    sort -u -o "$d/kept.sym" "$d/kept.sym" "$d/$idx.sym"
  done
  [ -f "$d/dropped" ] && dropped=$(wc -l < "$d/dropped")
  if [ "${dropped:-0}" -gt 0 ]; then
    echo "oft: merge: $dropped redundant archive(s) excluded; $(wc -l < "$keep") kept"
    sort "$keep" > "$list"
  fi
  return 0
}

oft_merge_archives() {
  local out="$BUILDDIR/lib/liboft.a"
  mkdir -p "$BUILDDIR/lib"
  rm -f "$out"
  local mri="$BUILDDIR/merge.mri" list="$BUILDDIR/merge-list.txt" n=0 a



  find "$BUILDDIR" -name '*.a' -type f -not -path "$BUILDDIR/lib/*" | sort > "$list"
  oft_drop_redundant_archives "$list"
  echo "create $out" > "$mri"
  while IFS= read -r a; do
    echo "addlib $a" >> "$mri"
    n=$((n + 1))
  done < "$list"




















  if [ "$n" -eq 0 ]; then







    find "$BUILDDIR" -mindepth 2 -name '*.o' -type f \
      -not -path "$BUILDDIR/lib/*" \
      -not -path '*/CMakeFiles/[0-9]*/*' \
      -not -path '*/CMakeScratch/*' -not -path '*/CMakeTmp/*' \
      -not -path '*TryCompile*' \
      | LC_ALL=C sort > "$list"
    n=$(wc -l < "$list")
    if [ "$n" -ge 1 ]; then
      xargs "$CHOST-ar" r "$out" < "$list"
      [ -f "$out" ] || { echo "oft: archiving $n loose object(s) produced no $out" >&2; return 1; }
      echo "oft: no .a from the build; archived $n loose object(s) into lib/liboft.a"
      LIB_ARCHIVE="lib/liboft.a"
      oft_add_sysroot_deps
      return 0
    fi
    echo "oft: the build produced no .a under $BUILDDIR" >&2; return 1
  fi
  printf 'save\nend\n' >> "$mri"
  "$CHOST-ar" -M < "$mri"
  [ -f "$out" ] || { echo "oft: merging $n archive(s) produced no $out" >&2; return 1; }
  echo "oft: merged $n archive(s) into lib/liboft.a"
  LIB_ARCHIVE="lib/liboft.a"
  oft_add_sysroot_deps
}



























































oft_single_entry() {
  local ar_file=$1 defs d n
  [ -f "$ar_file" ] || return 0
  defs=$("$CHOST-nm" -A --defined-only "$ar_file" 2>/dev/null          | awk '$0 ~ / T _?LLVMFuzzerTestOneInput$/ { sub(/^[^:]*:/, "", $1); sub(/:$/, "", $1); print $1 }')
  n=$(printf '%s\n' "$defs" | grep -c . || true)




  [ "${n:-0}" -eq 0 ] && return 0
  [ "${n:-0}" -eq 1 ] && [ "$defs" = "harness.o" ] && return 0
  for d in $defs; do
    case "$d" in harness.o) continue ;; esac
    if "$CHOST-ar" d "$ar_file" "$d"; then
      echo "oft: DROPPED archive member $d -- it defines LLVMFuzzerTestOneInput and is not the harness"            "(a sibling fuzzer body or a subproject's fuzzer archive); the linker would have taken it"            "instead of harness.o (measured: ots linked lz4's round_trip_stream_fuzzer)"
    else
      echo "oft: could not drop archive member $d, which defines LLVMFuzzerTestOneInput alongside harness.o" >&2
      return 1
    fi
  done
  defs=$("$CHOST-nm" -A --defined-only "$ar_file" 2>/dev/null          | awk '$0 ~ / T _?LLVMFuzzerTestOneInput$/ { sub(/^[^:]*:/, "", $1); sub(/:$/, "", $1); print $1 }')
  n=$(printf '%s\n' "$defs" | grep -c . || true)
  if [ "${n:-0}" -ne 1 ] || [ "$defs" != "harness.o" ]; then
    echo "oft: after dropping extra definers the archive still does not have harness.o as its ONLY"          "LLVMFuzzerTestOneInput definer (have: ${defs:-none}); refusing to link the wrong program" >&2
    return 1
  fi
  echo "oft: single-entry check: harness.o is now the only LLVMFuzzerTestOneInput definer"
}


oft_stub_gate() {
  local ar_file=$1 hobj=$2
  [ -f "$ar_file" ] && [ -f "$hobj" ] || return 0
  local lib_members
  lib_members=$("$CHOST-ar" t "$ar_file" | grep -cv -e '^harness\.o$' -e '^header-only-stub\.o$' || true)
  [ "${lib_members:-0}" -gt 0 ] || return 0
  local h_undef a_def
  h_undef=$("$CHOST-nm" -u "$hobj" | awk '{print $NF}' | sort -u)
  a_def=$("$CHOST-nm" --defined-only "$ar_file" 2>/dev/null \
        | awk 'NF>=3 && $(NF-1) ~ /^[TtDdRrBbWw]$/ {print $NF}' | sort -u)
  if [ -z "$h_undef" ]; then
    echo "oft: harness references nothing at all -- the stub signature; refusing" >&2
    return 1
  fi
  if [ -z "$a_def" ]; then
    echo "oft: stub gate skipped -- nm produced no defined symbols for the archive; cannot distinguish stub from broken instrument" >&2
    return 0
  fi
  local undef_hits
  undef_hits=$(comm -12 <(printf '%s\n' "$h_undef") <(printf '%s\n' "$a_def") | wc -l)
  if [ "$undef_hits" -eq 0 ]; then
    echo "oft: harness references NO symbol the library archive defines" >&2
    echo "  ($lib_members library member(s) present); refusing the build." >&2
    echo "  TWO CAUSES PRODUCE THIS, and the gate cannot tell them apart:" >&2
    echo "    1. a stub or feature probe rather than a real harness; or" >&2
    echo "    2. a real harness whose entry point is in a source file the" >&2
    echo "       project does NOT compile into its library -- check the" >&2
    echo "       project's own OSS-Fuzz build.sh for extra sources named" >&2
    echo "       against THIS fuzzer before believing cause 1." >&2
    return 1
  fi
  return 0
}
























oft_add_sysroot_deps() {
  local sysroot="${OFT_SYSROOT:-/opt/musl-sysroot}" d














































  for d in \
      libgio-2.0.a libgobject-2.0.a libgmodule-2.0.a libgthread-2.0.a \
      libglib-2.0.a libxml2.a libfontconfig.a libfreetype.a libhdf5_hl.a libhdf5.a \
      libevent.a libevent_core.a libevent_extra.a libevent_pthreads.a \
      libqpdf.a \
      libsystemd.a libcap.a libudev.a libmount.a libblkid.a \
      libturbojpeg.a libjpeg.a libpng16.a libogg.a libuuid.a \
      libpcre2-8.a libpcre2-16.a libpcre2-32.a libffi.a \
      libboost_log_setup.a libboost_log.a \
      libboost_wave.a libboost_graph.a \
      libboost_locale.a libboost_iostreams.a \
      libboost_unit_test_framework.a libboost_test_exec_monitor.a \
      libboost_prg_exec_monitor.a \
      libboost_fiber.a libboost_coroutine.a libboost_context.a \
      libboost_filesystem.a libboost_program_options.a libboost_serialization.a \
      libboost_wserialization.a libboost_regex.a libboost_url.a libboost_json.a \
      libboost_process.a libboost_thread.a libboost_timer.a libboost_chrono.a \
      libboost_date_time.a libboost_random.a libboost_charconv.a \
      libboost_container.a libboost_type_erasure.a libboost_contract.a \
      libboost_nowide.a libboost_math_tr1l.a libboost_math_tr1f.a \
      libboost_math_tr1.a libboost_math_c99l.a libboost_math_c99f.a \
      libboost_math_c99.a libboost_stacktrace_basic.a libboost_stacktrace_noop.a \
      libboost_atomic.a libboost_exception.a libboost_system.a \
      libbrotlidec.a libbrotlienc.a libbrotlicommon.a libzstd.a \
      libgnutls.a libhogweed.a libnettle.a libtasn1.a libgmp.a \
      libwolfssl.a libaprutil-1.a libapr-1.a libev.a libpcap.a \
      libusb-1.0.a libhwloc.a libgflags.a libzmq.a \
      libicuio.a libicui18n.a libicuuc.a libicudata.a \
      libleptonica.a libhwy.a libcbor.a libexpat.a \
      libnghttp2.a libcares.a libjson-c.a libb2.a libmd.a \
      libreadline.a libhistory.a libformw.a libmenuw.a libpanelw.a \
      libncursesw.a \
      liburcu-cds.a liburcu.a liburcu-common.a liblmdb.a \
      libuv.a libcjson.a libqb.a \
      libprotobuf.a libprotobuf-lite.a libprotobuf-c.a \
      libcups.a libdns_sd.a libtiff.a liblcms2.a \
      libbotan-2.a libINIReader.a libinih.a \
      libssl.a libcrypto.a \
      libgc.a \
      libelf.a libbz2.a liblzma.a libz.a; do
    if [ -f "$sysroot/usr/lib/$d" ]; then
      LIB_EXTRA="${LIB_EXTRA:-} $sysroot/usr/lib/$d"
    fi
  done
  [ -n "${LIB_EXTRA:-}" ] && echo "oft: sysroot dependencies on the link line:${LIB_EXTRA}"
  return 0
}









































oft_gnulib_bootstrap() {
  local src="$BUILDDIR/src" boot="$BUILDDIR/src/bootstrap"
  [ -f "$boot" ] || return 0



  grep -q gnulib "$boot" 2>/dev/null || return 0
  local gl="" d
  for d in gnulib .gnulib; do
    if [ -f "$src/$d/gnulib-tool" ]; then gl="$src/$d"; break; fi
  done
  if [ -z "$gl" ]; then















    for d in gnulib .gnulib; do
      if [ -d "$src/$d" ]; then
        echo "oft: FATAL: $src/$d exists but carries no gnulib-tool -- an EMPTY or" >&2
        echo "  partial gnulib checkout, not a missing one. provision_gnulib did not" >&2
        echo "  complete (it races when sibling targets share one bare cache). This is" >&2
        echo "  sticky: fetch_target early-returns on a matching COMMIT, so retrying" >&2
        echo "  changes nothing. Clear the tree and re-run:  rm -rf -- \"ext/\${t:?}\"" >&2
        echo "  Scan for others:  for d in ext/*/src/gnulib; do [ \"\$(ls -A \"\$d\" 2>/dev/null | wc -l)\" -eq 0 ] && echo \"EMPTY \$d\"; done" >&2
        return 1
      fi
    done
    echo "oft: gnulib bootstrap needs a gnulib checkout the tree does not carry (bootstrap would clone from the network)" >&2
    return 0
  fi
  local opts=""
  if grep -q -- --no-git "$boot"; then


    opts="--no-git --gnulib-srcdir=$gl"
    grep -q -- --skip-po "$boot" && opts="$opts --skip-po"
    echo "oft: running ./bootstrap $opts"

    ( cd "$src" && export GNULIB_SRCDIR="$gl" && \
      if [ -x ./bootstrap ]; then ./bootstrap $opts; else sh ./bootstrap $opts; fi ) \
      || { echo "oft: bootstrap failed" >&2; return 0; }
  else








    echo "oft: running ./bootstrap bare (script predates --no-git; its submodule path is $gl)"
    ( cd "$src" && unset GNULIB_SRCDIR && \
      if [ -x ./bootstrap ]; then ./bootstrap; else sh ./bootstrap; fi ) \
      || { echo "oft: bootstrap failed" >&2; return 0; }
  fi
  return 0
}


































oft_build_autotools() {
  oft_copy_src
  local sroot="$BUILDDIR/src${OFT_BUILD_SUBDIR:+/$OFT_BUILD_SUBDIR}"
  [ -d "$sroot" ] || {
    echo "oft: OFT_BUILD_SUBDIR=$OFT_BUILD_SUBDIR names no directory in the tree" >&2
    return 1
  }
  [ -n "${OFT_BUILD_SUBDIR:-}" ] && echo "oft: configuring from subdirectory $OFT_BUILD_SUBDIR"
  if [ ! -x "$sroot/configure" ]; then




    oft_gnulib_bootstrap
  fi
  if [ ! -x "$sroot/configure" ]; then
    if command -v autoreconf >/dev/null 2>&1; then
      echo "oft: no generated ./configure; running autoreconf -fi"
      ( cd "$sroot" && { [ -x ./autogen.sh ] && NOCONFIGURE=1 ./autogen.sh || autoreconf -fi; } ) \
        || { echo "oft: autoreconf failed" >&2; return 1; }
    fi
  fi
  [ -x "$sroot/configure" ] || {
    echo "oft: no generated ./configure in the pinned tree and no autoreconf on this image" >&2
    return 1
  }
  ( cd "$sroot" \
    && CHOST="$CHOST" CC="$CC" CFLAGS="$CFLAGS" \
       CC_FOR_BUILD=/usr/bin/cc CFLAGS_FOR_BUILD="-O2" \
       CXX="$(oft_cxx)" CXXFLAGS="$(oft_cxxflags)" \
       ./configure --host="$CHOST" --build=x86_64-pc-linux-gnu \
         --enable-static --disable-shared --prefix="${OFT_PREFIX:?build.sh sets the flavour-independent install prefix; see oft_link_prefix}" "$@" \
    && oft_make_then_keep_going \
    && { make install || true; } )
  oft_merge_archives
}





















oft_build_blind() {
  oft_copy_src
  local root="$BUILDDIR/src"



  local dirs="$root" d
  if [ $# -gt 0 ]; then
    dirs=""
    for d in "$@"; do dirs="$dirs $root/$d"; done
  fi

  local objdir="$BUILDDIR/obj"
  rm -rf "$objdir"; mkdir -p "$objdir"




  : > "$BUILDDIR/blind-errors.txt"

  local inc="" fixedd=""
  local i
  for i in "$root" "$root/include" "$root/src" "$root/lib" ${OFT_BLIND_INCLUDE:-}; do
    case "$i" in /*) ;; *) i="$root/$i" ;; esac
    [ -d "$i" ] && { inc="$inc -I$i"; fixedd="$fixedd $i"; }
  done










  inc="$inc $(oft_sweep_includes demote $fixedd)"

  local ok=0 skipped=0 n=0 f rel obj lang
  local list="$BUILDDIR/blind-sources.txt"










































































  find $dirs -type f \
    \( -name '*.c' -o -name '*.cc' -o -name '*.cpp' -o -name '*.cxx' \) \
    -not -path '*/test/*' -not -path '*/tests/*' -not -path '*/Tests/*' \
    -not -path '*/example/*' -not -path '*/examples/*' \
    -not -path '*/bench/*' -not -path '*/benchmark*/*' \
    -not -path '*/fuzz/*' -not -path '*/fuzzer*/*' -not -path '*/oss-fuzz/*' \
    -not -path '*/doc/*' -not -path '*/docs/*' \
    -not -path '*/contrib/*' -not -path '*/third_party/*' \
    -not -path '*/thirdparty/*' \
    -not -path '*/cmake/*' -not -path '*/tools/*' -not -path '*/extras/*' \
    -not -path '*/attic/*' -not -path '*/web/*' -not -path '*/inspector/*' \
    -not -path '*/nonunix/*' -not -path '*/win32/*' -not -path '*/win64/*' \
    -not -path '*/windows/*' -not -path '*/msvc/*' -not -path '*/darwin/*' \
    -not -path '*/mingw/*' \
    -not -name '*_test.*' -not -name 'test_*' \
    -not -name '*fuzz*' \
    | sort > "$list"



  n=$(wc -l < "$list")
  [ "$n" -ge 1 ] || { echo "oft: blind recipe found no C/C++ sources under $dirs" >&2; return 1; }





  if grep -qE '\.(cc|cpp|cxx)$' "$list"; then
    oft_require_target_cxx || return 1
  fi


































  local work="$objdir/.blind" worker jobs i st
  mkdir -p "$work"
  worker="$work/compile1.sh"
  cat > "$worker" <<'EOW'
#!/bin/sh




root=$1 objdir=$2 work=$3 idx=$4 f=$5
rel=${f#"$root"/}
obj="$objdir/$(printf '%s' "$rel" | tr '/' '_')"
obj="${obj%.*}.o"
err="$work/$idx.err"
: > "$err"
case "$f" in
  *.cc|*.cpp|*.cxx) lang="-stdlib=libc++" ;;
  *) lang="" ;;
esac

if [ -z "$lang" ] && "$CC" $CFLAGS $OFT_BLIND_INC ${OFT_BLIND_CFLAGS:-} -c "$f" -o "$obj" 2>>"$err"; then
  st=ok
elif [ -n "$lang" ] && { "$CC" $CFLAGS $lang -std=c++17 $OFT_BLIND_INC ${OFT_BLIND_CFLAGS:-} -c "$f" -o "$obj" 2>>"$err" \
    || "$CC" $CFLAGS $lang -std=c++20 $OFT_BLIND_INC ${OFT_BLIND_CFLAGS:-} -c "$f" -o "$obj" 2>>"$err"; }; then
  st=ok
else
  st=fail
fi
printf '%s\n' "$st" > "$work/$idx.st"
[ "$st" = ok ] || [ "${OFT_BLIND_SKIP:-0}" = 1 ] || exit 255
exit 0
EOW



  awk -v root="$root/" '{ rel = substr($0, length(root) + 1); gsub("/", "_", rel); sub(/\.[^.]*$/, "", rel); print NR "\t" rel ".o" }' \
    "$list" > "$work/keys"
  cut -f2 "$work/keys" | sort | uniq -d > "$work/dupkeys"
  jobs=$(oft_jobs)
  local t0
  t0=$(date +%s)










  local xrc=0
  if i=0; while IFS= read -r f; do
        i=$((i + 1))
        if [ -s "$work/dupkeys" ] && grep -qxF -- "$(sed -n "${i}p" "$work/keys" | cut -f2)" "$work/dupkeys"; then
          continue
        fi
        printf '%s\0%s\0' "$i" "$f"
      done < "$list" | OFT_BLIND_INC="$inc" OFT_BLIND_CFLAGS="${OFT_BLIND_CFLAGS:-}" OFT_BLIND_SKIP="${OFT_BLIND_SKIP:-0}" \
        xargs -0 -n 2 -P "$jobs" sh "$worker" "$root" "$objdir" "$work" 2> "$work/xargs.err"; then
    xrc=0
  else
    xrc=$?
  fi
  case "$xrc" in
    0|124) ;;
    *) echo "oft: blind recipe: parallel compile fan-out failed (xargs exit $xrc)" >&2
       cat "$work/xargs.err" >&2; return 1 ;;
  esac



  if [ -s "$work/dupkeys" ] && [ "$xrc" -eq 0 ]; then
    i=0
    while IFS= read -r f; do
      i=$((i + 1))
      if grep -qxF -- "$(sed -n "${i}p" "$work/keys" | cut -f2)" "$work/dupkeys"; then


        OFT_BLIND_INC="$inc" OFT_BLIND_CFLAGS="${OFT_BLIND_CFLAGS:-}" OFT_BLIND_SKIP="${OFT_BLIND_SKIP:-0}" \
          sh "$worker" "$root" "$objdir" "$work" "$i" "$f" || break
      fi
    done < "$list"
  fi


  i=0
  while IFS= read -r f; do
    i=$((i + 1))
    rel=${f#"$root"/}
    st="$work/$i.st"
    if [ ! -f "$st" ]; then





      OFT_BLIND_INC="$inc" OFT_BLIND_CFLAGS="${OFT_BLIND_CFLAGS:-}" OFT_BLIND_SKIP="${OFT_BLIND_SKIP:-0}" \
          sh "$worker" "$root" "$objdir" "$work" "$i" "$f" || :
    fi
    [ -f "$st" ] || { echo "oft: blind recipe: no compile status for $rel (internal error)" >&2; return 1; }
    cat "$work/$i.err" >> "$BUILDDIR/blind-errors.txt"
    case "$(cat "$st")" in
      ok) ok=$((ok + 1)) ;;
      fail)
        if [ "${OFT_BLIND_SKIP:-0}" = 1 ]; then
          skipped=$((skipped + 1))
        else
          echo "oft: blind recipe: $rel failed to compile (see blind-errors.txt); OFT_BLIND_SKIP=1 to skip" >&2
          tail -20 "$BUILDDIR/blind-errors.txt" >&2
          return 1
        fi ;;
      *) echo "oft: blind recipe: unreadable compile status for $rel (internal error)" >&2; return 1 ;;
    esac
  done < "$list"


  echo "oft: blind recipe: compile phase $(( $(date +%s) - t0 )) s with $jobs jobs"

  [ "$ok" -ge 1 ] || { echo "oft: blind recipe compiled 0 of $n sources" >&2; return 1; }
  echo "oft: blind recipe compiled $ok of $n sources ($skipped skipped)"
  printf '%s %s %s\n' "$ok" "$skipped" "$n" > "$BUILDDIR/blind-counts.txt"

  mkdir -p "$BUILDDIR/lib"
  rm -f "$BUILDDIR/lib/liboft.a"
  "$CHOST-ar" crs "$BUILDDIR/lib/liboft.a" "$objdir"/*.o
  "$CHOST-nm" "$BUILDDIR/lib/liboft.a" > /dev/null
  LIB_ARCHIVE="lib/liboft.a"



  oft_add_sysroot_deps
}













OFT_LIBC_HEADERS='
assert.h complex.h ctype.h endian.h errno.h err.h fcntl.h fenv.h float.h inttypes.h
iso646.h limits.h locale.h math.h memory.h netdb.h poll.h pthread.h sched.h
setjmp.h signal.h stdalign.h stdarg.h stdatomic.h stdbool.h stddef.h stdint.h
stdio.h stdlib.h stdnoreturn.h string.h strings.h tgmath.h threads.h time.h
uchar.h unistd.h wchar.h wctype.h
'






OFT_LIBC_SYS_HEADERS='
file.h ioctl.h mman.h param.h resource.h select.h socket.h stat.h time.h
types.h uio.h un.h utsname.h wait.h
'




































oft_dir_shadows_libc() {
  local dir=$1 h
  for h in $OFT_LIBC_HEADERS; do
    if [ -e "$dir/$h" ] || [ -e "$dir/bits/$h" ]; then
      return 0
    fi
  done




  for h in $OFT_LIBC_SYS_HEADERS; do
    if [ -e "$dir/sys/$h" ]; then
      return 0
    fi
    if [ "$(basename "$dir")" = sys ] && [ -e "$dir/$h" ]; then
      return 0
    fi
  done
  return 1
}

























oft_sweep_includes() {










  local mode=$1 hd a dirs
  shift || true
  local fixed=" $* "
  dirs=$(find "$BUILDDIR/src" "$BUILDDIR/cmk" "$BUILDDIR/mes" "$BUILDDIR/include" \
                -maxdepth 5 \( -name '*.h' -o -name '*.hh' -o -name '*.hpp' -o -name '*.hxx' \) -type f \
                -not -path '*/.git/*' -not -path '*/third_party/*' \
                -not -path '*/thirdparty/*' \
                -not -path '*/vendor/*' -not -path '*/_deps/*' \
                -not -path '*/subprojects/*' -not -path '*/external/*' \
                -not -path '*/nonunix/*' -not -path '*/win32/*' \
                -not -path '*/windows/*' -not -path '*/msvc/*' \
                -not -path '*/darwin/*' -not -path '*/mingw/*' \
                2>/dev/null | sed 's|/[^/]*$||' | sort -u)
  for hd in $dirs; do
    if [ "$mode" = demote ] || oft_dir_shadows_libc "$hd"; then
      case "$fixed" in *" $hd "*) continue ;; esac
      printf ' -idirafter %s' "$hd"
    else
      printf ' -I%s' "$hd"
    fi
  done



  { echo "$dirs" | sed 's|/[^/]*$||'
    echo "$dirs" | sed 's|/[^/]*$||;s|/[^/]*$||'; } | sort -u | while read -r a; do
    case "$a" in "$BUILDDIR"/*) ;; *) continue ;; esac
    case "$fixed" in *" $a "*) continue ;; esac
    echo "$dirs" | grep -qxF "$a" && continue
    printf ' -idirafter %s' "$a"
  done









  local vdirs
  vdirs=$(find "$BUILDDIR/src" "$BUILDDIR/cmk" "$BUILDDIR/mes" "$BUILDDIR/include" \
                -maxdepth 5 \( -name '*.h' -o -name '*.hh' -o -name '*.hpp' -o -name '*.hxx' \) -type f \
                \( -path '*/third_party/*' -o -path '*/thirdparty/*' -o -path '*/vendor/*' \
                   -o -path '*/_deps/*' -o -path '*/subprojects/*' \
                   -o -path '*/external/*' \) \
                -not -path '*/.git/*' \
                -not -path '*/nonunix/*' -not -path '*/win32/*' \
                -not -path '*/windows/*' -not -path '*/msvc/*' \
                -not -path '*/darwin/*' -not -path '*/mingw/*' \
                2>/dev/null | sed 's|/[^/]*$||' | sort -u)
  [ -n "$vdirs" ] || return 0
  { echo "$vdirs"
    echo "$vdirs" | sed 's|/[^/]*$||'
    echo "$vdirs" | sed 's|/[^/]*$||;s|/[^/]*$||'; } | sort -u | while read -r a; do
    case "$a" in "$BUILDDIR"/*) ;; *) continue ;; esac
    case "$fixed" in *" $a "*) continue ;; esac
    printf ' -idirafter %s' "$a"
  done
}


































oft_note_generator_inputs() {
  local root="${1:-$BUILDDIR/src}" n first
  [ -d "$root" ] || return 0
  n=$(find "$root" \( -name '*.y' -o -name '*.ypp' -o -name '*.yy' \
                    -o -name '*.l' -o -name '*.lpp' -o -name '*.ll' \) \
        -type f -not -path '*/.git/*' 2>/dev/null | wc -l)
  [ "$n" -ge 1 ] || return 0
  first=$(find "$root" \( -name '*.y' -o -name '*.l' \) -type f \
            -not -path '*/.git/*' 2>/dev/null | head -1 | sed "s|^$root/||")
  echo "oft: generator inputs present: $n (e.g. ${first:-?})"
  echo "     if the link fails on undefined symbols, suspect ungenerated sources"
}

oft_build_harness() {
  local src=$1; shift
  oft_note_generator_inputs
  local p
  for p in "$BUILDDIR/src/$src" "/work/targets/$T/$src" "$src"; do
    [ -f "$p" ] && { src=$p; break; }
  done
  [ -f "$src" ] || { echo "oft: harness source not found: $1" >&2; return 1; }












  local langflags=""
  case "$src" in
    *.cc|*.cpp|*.cxx|*.C|*.c++|*.cc.in|*.hpp)




      langflags="-x c++ -stdlib=libc++"



      oft_require_target_cxx || return 1
      LIB_EXTRA="${LIB_EXTRA:-} $OFT_CXX_RUNTIME"
      ;;
  esac
  local inc="-I$BUILDDIR/src -I$BUILDDIR/src/include -I$BUILDDIR/src/src"

  inc="$inc -I$BUILDDIR/include -I$BUILDDIR/cmk -I$BUILDDIR/cmk/include"
  inc="$inc -I$BUILDDIR/mes -I$BUILDDIR/mes/include -I$(dirname "$src")"



































  inc="$inc $(oft_sweep_includes promote \
    "$BUILDDIR/src" "$BUILDDIR/src/include" "$BUILDDIR/src/src" \
    "$BUILDDIR/include" "$BUILDDIR/cmk" "$BUILDDIR/cmk/include" \
    "$BUILDDIR/mes" "$BUILDDIR/mes/include" "$(dirname "$src")")"










  local std rc=1 cfg









  for cfg in "" "-include $BUILDDIR/mes/config.h"; do
    if [ -n "$cfg" ]; then
      [ -f "$BUILDDIR/mes/config.h" ] || break
      echo "oft: harness retrying with meson-generated config.h (-include)"
    fi

  for std in ${OFT_CXX_STD:-} -std=c++17 -std=c++20 -std=c++23; do
    [ -n "$std" ] || continue
    case "$langflags" in
      *-x\ c++*) ;;
      *) std="" ;;                                               
    esac

    if "$CC" $CFLAGS $langflags $std $inc $cfg ${OFT_HARNESS_CFLAGS:-} "$@" \
         -c "$src" -o "$BUILDDIR/harness.o" 2>"$BUILDDIR/harness-cc.err"; then
      rc=0
      [ -n "$std" ] && echo "oft: harness compiled with $std"
      break
    fi
    [ -n "$std" ] || break
    [ -n "${OFT_CXX_STD:-}" ] && break
  done
    [ "$rc" = 0 ] && break
  done
  if [ "$rc" != 0 ]; then
    cat "$BUILDDIR/harness-cc.err" >&2
    return 1
  fi







  "$CHOST-nm" "$BUILDDIR/harness.o" | grep -q ' T LLVMFuzzerTestOneInput$' || {
    echo "oft: $1 compiled but defines no unmangled LLVMFuzzerTestOneInput" >&2
    "$CHOST-nm" "$BUILDDIR/harness.o" | grep -i fuzzer | head -5 >&2
    return 1
  }









  if [ -f "$BUILDDIR/lib/liboft.a" ]; then
    "$CHOST-ar" r "$BUILDDIR/lib/liboft.a" "$BUILDDIR/harness.o"

  else
    echo "oft: no lib/liboft.a to add the harness to -- recipe did not run?" >&2
    return 1
  fi











  local sdir comp cobj clang
  sdir=$(dirname "$src")
  for comp in ${OFT_COMPANION_SRCS:-}; do
    comp="$sdir/$comp"
    [ -f "$comp" ] || { echo "oft: companion $comp named in the pin but absent" >&2; return 1; }



    grep -q LLVMFuzzerTestOneInput "$comp" && continue
    cobj="$BUILDDIR/companion-$(basename "$comp").o"
    cobj="${cobj%.*}.o"
    clang=""
    case "$comp" in *.cc|*.cpp|*.cxx) clang="-x c++ -stdlib=libc++ ${std:-}" ;; esac

    "$CC" $CFLAGS $clang $inc ${OFT_HARNESS_CFLAGS:-} -c "$comp" -o "$cobj" || {
      echo "oft: companion $(basename "$comp") failed to compile" >&2
      return 1
    }
    "$CHOST-ar" r "$BUILDDIR/lib/liboft.a" "$cobj"
    echo "oft: companion $(basename "$comp") compiled into the archive"
  done

































  local sibdir sib sibobj siblang nsib=0
  sibdir=$(dirname "$src")
  case "$sibdir" in
    "$BUILDDIR/src"|"$BUILDDIR/src"/*) ;;                                
    *) sibdir="" ;;                                                            
  esac
  for sib in ${sibdir:+"$sibdir"/*.c "$sibdir"/*.cc "$sibdir"/*.cpp "$sibdir"/*.cxx}; do
    [ -f "$sib" ] || continue
    [ "$sib" = "$src" ] && continue
    grep -q 'LLVMFuzzerTestOneInput' "$sib" && continue
    grep -qE '^[[:space:]]*int[[:space:]]+main[[:space:]]*\(' "$sib" && continue
    siblang=""
    case "$sib" in
      *.cc|*.cpp|*.cxx) siblang="-x c++ -stdlib=libc++ ${std:-}" ;;
    esac
    sibobj="$BUILDDIR/oftsib-$(basename "$sib" | sed 's/\.[^.]*$//').o"

    if "$CC" $CFLAGS $siblang $inc ${OFT_HARNESS_CFLAGS:-} "$@" \
         -c "$sib" -o "$sibobj" 2>"$BUILDDIR/sib-cc.err"; then
      "$CHOST-ar" r "$BUILDDIR/lib/liboft.a" "$sibobj"
      nsib=$((nsib + 1))
      echo "oft: harness sibling archived: $(basename "$sib")"
    else
      echo "oft: harness sibling failed to compile, skipped: $(basename "$sib")"
      head -3 "$BUILDDIR/sib-cc.err"
    fi
  done
  [ "$nsib" -gt 0 ] && echo "oft: $nsib harness sibling(s) added to lib/liboft.a"


















  case " ${LIB_EXTRA:-} " in
    *libc++.a*) ;;                                                         
    *)
      if "$CHOST-nm" --undefined-only "$BUILDDIR/lib/liboft.a" 2>/dev/null \
           | grep -qE '_Znwm|_Znam|_ZdlPv|__cxa_|_ZNSt|_ZSt|_Unwind_'; then
        echo "oft: the archive needs the C++ runtime (undefined operator new/__cxa_*/std::)"
        oft_require_target_cxx || return 1
        LIB_EXTRA="${LIB_EXTRA:-} $OFT_CXX_RUNTIME"
      fi
      ;;
  esac
}












oft_build_meson() {
  command -v meson >/dev/null 2>&1 || {
    echo "oft: meson is not on this image (use the derived builder image)" >&2
    return 1
  }
  oft_copy_src
  local x="$BUILDDIR/cross.ini" f args="" cxxargs=""
  for f in $CFLAGS; do args="$args'$f', "; done


  for f in $(oft_cxxflags); do cxxargs="$cxxargs'$f', "; done

























  local prefer=true
  [ "${OFT_MESON_PREFER_STATIC:-1}" = 0 ] && prefer=false
  cat > "$x" <<EOX
[binaries]
c = '$CC'
cpp = '$(oft_cxx)'
ar = '$CHOST-ar'
strip = '$CHOST-strip'
nm = '$CHOST-nm'
pkg-config = 'pkg-config'

[host_machine]
system = 'linux'
cpu_family = 'riscv64'
cpu = 'riscv64'
endian = 'little'

[built-in options]
c_args = [$args]
cpp_args = [$cxxargs]
c_link_args = [$args]
default_library = 'static'
prefer_static = $prefer
EOX
  local msub="$BUILDDIR/src${OFT_BUILD_SUBDIR:+/$OFT_BUILD_SUBDIR}"
  [ -d "$msub" ] || { echo "oft: meson source dir $msub does not exist" >&2; return 1; }






  if [ -d "$BUILDDIR/mes" ] && ! cmp -s -- "$x" "$BUILDDIR/mes/.cross.ini.applied"; then
    echo "oft: cross.ini differs from the one mes/ was configured with -- wiping mes/ so the new flags apply" >&2
    rm -rf -- "${BUILDDIR:?}/mes"
  fi
  ( cd "$msub" \
    && meson setup "$BUILDDIR/mes" --cross-file "$x" \
         --default-library=static --prefix="${OFT_PREFIX:?build.sh sets the flavour-independent install prefix; see oft_link_prefix}" "$@" \
    && cp -- "$x" "$BUILDDIR/mes/.cross.ini.applied" \
    && ninja -C "$BUILDDIR/mes" -j "$(oft_jobs)" ) || {



      echo "oft: ninja default target failed; retrying with -k 0" >&2
      echo "ninja failed, retried with -k 0" > "$BUILDDIR/partial-build"
      ninja -C "$BUILDDIR/mes" -j "$(oft_jobs)" -k 0 2>&1 | tee "$BUILDDIR/keep-going.log" || true
      oft_keep_going_record ninja "$BUILDDIR/keep-going.log"
    }
  oft_merge_archives
}




















oft_seal_getenv() {












  if [ "${OFT_SEAL_GETENV:-1}" = 0 ]; then
    echo "oft: getenv seal SKIPPED (OFT_SEAL_GETENV=0) -- this build reads the"
    echo "     real environment, and is the -env half of the pair"
    return 0
  fi
  local obj="$BUILDDIR/wrap_getenv.o"

  "${DRVCC:?build.sh must export DRVCC}" ${BASE_CFLAGS} -c /work/src/wrap_getenv.c -o "$obj" || return 1
  "$CHOST-nm" "$obj" | grep -q ' T __wrap_getenv$' || {
    echo "oft: wrap_getenv.o defines no __wrap_getenv" >&2
    return 1
  }
  LIB_EXTRA="${LIB_EXTRA:-} $obj -Wl,--wrap=getenv"
}




























oft_seal_getpid() {
  local obj="$BUILDDIR/wrap_getpid.o"

  "${DRVCC:?build.sh must export DRVCC}" ${BASE_CFLAGS} -c /work/src/wrap_getpid.c -o "$obj" || return 1
  "$CHOST-nm" "$obj" | grep -q ' T __wrap_getpid$' || {
    echo "oft: wrap_getpid.o defines no __wrap_getpid" >&2
    return 1
  }
  LIB_EXTRA="${LIB_EXTRA:-} $obj -Wl,--wrap=getpid -Wl,--wrap=getppid"
}

oft_seal_mkstemp() {
  local obj="$BUILDDIR/wrap_mkstemp.o"

  "${DRVCC:?build.sh must export DRVCC}" ${BASE_CFLAGS} -c /work/src/wrap_mkstemp.c -o "$obj" || return 1
  "$CHOST-nm" "$obj" | grep -q ' T __wrap_mkstemp$' || {
    echo "oft: wrap_mkstemp.o defines no __wrap_mkstemp" >&2
    return 1
  }
  LIB_EXTRA="${LIB_EXTRA:-} $obj -Wl,--wrap=mkstemp -Wl,--wrap=mkostemp"
  LIB_EXTRA="$LIB_EXTRA -Wl,--wrap=mkstemps -Wl,--wrap=mkostemps"
}




































oft_use_fortran() {
  local fl=/opt/oft-fortran/bin/flang cfg=/opt/oft-fortran/flang-musl.cfg lib=/opt/oft-fortran/lib fc
  if [ ! -x "$fl" ] || [ ! -f "$cfg" ] || [ ! -f "$lib/libFortranRuntime.a" ] || [ ! -f "$lib/libFortranDecimal.a" ]; then
    echo "oft: no-fortran-toolchain -- $T calls oft_use_fortran but this image has no /opt/oft-fortran" >&2
    echo "  (a Fortran pin needs BUILD_IMAGE=fortran-builder, an image with a Fortran compiler)" >&2
    return 1
  fi
  if [ "${FLAV:-}" = gcc ]; then
    echo "oft: oft_use_fortran: the gcc flavour has no Fortran toolchain" >&2
    return 1
  fi
  [ -n "${SHIM:-}" ] && [ -d "$SHIM" ] || { echo "oft: oft_use_fortran needs build.sh's compiler shim dir (\$SHIM)" >&2; return 1; }
  [ -n "${OFT_ARCH_PIN:-}" ] || { echo "oft: oft_use_fortran needs build.sh's OFT_ARCH_PIN" >&2; return 1; }
  fc="$SHIM/$CHOST-flang"
  { printf '#!/bin/sh\n%s\n' "$OFT_ARCH_PIN"
    printf 'nogc="-Wl,--no-gc-sections"; for a in "$@"; do case "$a" in -c|-E|-S|-fsyntax-only|-M|-MM|--version|-dumpmachine|-print-*) nogc=;; esac; done\n'
    printf 'exec %s --config=%s%s $nogc "$@"\n' "$fl" "$cfg" "${OFT_SYSROOT_FLAG:-}"
  } > "$fc"
  chmod +x "$fc"
  FC=$fc; F77=$fc; export FC F77
  LIB_EXTRA="${LIB_EXTRA:-} $lib/libFortranRuntime.a $lib/libFortranDecimal.a"
  echo "oft: fortran: FC=F77=$fc ($("$fl" --version | head -1)); runtime archives on the link line"
}
