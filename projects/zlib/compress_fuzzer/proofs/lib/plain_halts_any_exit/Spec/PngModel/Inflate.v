(** * Spec.PngModel.Inflate — transcription of zlib-1.3.1's [inflate].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.{Base, ZBitsIn, Checksum, Inftrees, InflateFast}] and
    Stdlib.

    Source: [materials/zlib-1.3.1/inflate.c] (in-container
    [/harness/problem/materials/zlib-1.3.1/inflate.c]) — the lifecycle
    entry points [inflateResetKeep] / [inflateReset] / [inflateReset2] /
    [inflateInit2_] / [inflateEnd] ([:105-207], [:1245-1256]),
    [fixedtables] ([:245-290]), [updatewindow] ([:365-412]) and the
    [for (;;) switch (state->mode)] mode machine ([:585-1241]) with its
    [inf_leave] epilogue ([:1243-1273]).  [inffixed.h] is transcribed here
    because [inflate.c] is what [#include]s it ([:283]).

    BUG-FOR-BUG, and the deviations from a clean-room inflate that this
    file exists to pin:

    1. [inflateInit2(strm, 0)] is what libpng asks for ([pngrutil.c:415],
       and [inflateReset2(strm, 0)] at [:406] on every later chunk), so
       [inflateReset2] computes [wrap = (0 >> 4) + 5 = 5] and
       [windowBits &= 15 = 0] ([inflate.c:155-159]).  Consequences that
       run through the whole file:
         - [wrap & 2 == 0], so the gzip-magic test at [:617] can never
           fire and the arms FLAGS/TIME/OS/EXLEN/EXTRA/NAME/COMMENT/HCRC
           are DEAD (see the dead-arm finding below);
         - [wrap & 1 != 0], so the zlib header check IS performed;
         - [wrap & 4 != 0], so the ADLER-32 trailer IS validated;
         - [wbits = 0], so the HEAD arm takes the window size from the
           stream's own CINFO nibble ([:636-637]) — which is exactly the
           byte [Spec/PngModel/Chunk.v]'s [optimize_cmf] rewrites, so
           [wsize] here is [emitted_window] there, in [256 .. 32768], NOT
           a constant 32768.
    2. [INFLATE_STRICT] is not defined ([materials/Makefile:18] passes only
       [-O2 -static -no-pie]), so DISTEXT's [offset > dmax] rejection
       ([:1121-1127]) is compiled out.  [dmax] is computed and stored and
       then never read.
    3. [INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR] is not defined either
       (note this vendored copy's [_ARRR] spelling), so MATCH's zero-fill
       arm ([:1138-1150]) is compiled out, leaving
       [[if (copy > whave) { if (sane) { BAD; break; } }]] with an EMPTY
       else.  [sane] is 1 from [inflateResetKeep] ([:120]) and only
       [inflateUndermine] clears it, which libpng never calls, so the
       fall-through is dead — transcribed anyway.
    4. [PKZIP_BUG_WORKAROUND] is not defined, so TABLE's
       [nlen > 286 || ndist > 30] rejection ([:900-905]) IS active.
    5. The [state->head] arms ([:623-624], [:667-668], [:702-705],
       [:717-718], [:752-756], [:775-779], [:800-803]) are all dead:
       [head] is [Z_NULL] from [inflateResetKeep] ([:117]) and only
       [inflateGetHeader] sets it, which libpng never calls.
    6. [flush] is only ever [Z_NO_FLUSH], [Z_SYNC_FLUSH] or [Z_FINISH]
       ([pngrutil.c:563-564], [:814], [:4225]), so the [Z_BLOCK]/[Z_TREES]
       early exits at [:826], [:846-849], [:871] and [:1021] are dead.
       Transcribed, because the theorem is universally quantified.
    7. The [ret = inflate_table(...)] assignments ([:920], [:1003],
       [:1012]) CLOBBER the [ret] local that [inf_leave] returns.  On the
       success path they store 0, which happens to equal [Z_OK]; the model
       stores the same value rather than pretending [ret] is untouched.
    8. [inflate_state] is [ZALLOC]ed and NOT zeroed ([:190]; libpng's
       [png_zalloc] is a plain [png_malloc_warn]), and [inflateResetKeep]
       ([:105-127]) does not write eleven of its fields: [check], [length],
       [offset], [extra], [lenbits], [distbits], [ncode], [nlen], [ndist],
       [have], [was], nor [lens[320]] or [work[288]].  Every one of them
       holds allocator garbage until the mode machine first assigns it.
       [check] is the surprising member of that list — it is reset only in
       the HEAD arm ([:641]), so a stream that fails its header check
       leaves [state->check] holding whatever the allocator left, and
       [inf_leave]'s [UPDATE_CHECK] ([:1264]) would fold that garbage in
       if [out] were nonzero.  Confirmed empirically: the delivered musl
       binary and an independent glibc/Debian riscv64 build of the same
       sources disagree on exactly these eleven fields (and on [lens]) in
       ~1500 of 6620 recorded calls, and on nothing else.  The model
       therefore takes all eleven as INPUTS of a call rather than
       assuming a reset value.

    9. [out] is the C's own double duty: the [avail_out] snapshot at entry
       AND, after the CHECK arm's [out -= left; ... out = left]
       ([:1194-1201]), a fresh snapshot — so that [inf_leave] does not
       count the same output bytes into the ADLER twice.  Transcribed as
       written; [q_out] is that one variable.

    DEAD-ARM FINDING (requested explicitly, and load-bearing for the size
    of the machine-level walk).  With [wrap = 5] and [head = Z_NULL] the
    reachable mode set for THIS driver is

      HEAD, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
      LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT,
      CHECK, LENGTH, DONE, BAD, MEM

    and the dead ones are

      FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC   [wrap & 2 == 0]
      SYNC and the [default:] label                        [inflateSync is
                                                            never called,
                                                            and [mode] is
                                                            always one of
                                                            the enum's
                                                            32 values]

    Two of the "reachable" ones deserve a note.  LENGTH is reached (it is
    CHECK's fallthrough) but its BODY is dead: it is gated on
    [state->wrap && state->flags], and [flags] is 0 for a zlib stream
    ([:642]).  MEM is reachable only if the window [ZALLOC] fails
    ([:375-379]); the model carries that as the [n_walloc] parameter
    rather than simulating an allocator, per the campaign's call-boundary
    convention.  DICTID/DICT ARE reachable: the fuzz driver feeds
    attacker-chosen IDAT bytes to the decoder, and a header with FDICT set
    ([:645]) takes DICTID -> DICT -> [return Z_NEED_DICT] since libpng
    never calls [inflateSetDictionary].

    Style follows [Spec/PngModel/Inftrees.v]: C line-number citations at
    every phase; [nat]-fuelled [Fixpoint]s whose fuel is a static bound
    read off the same C loop; a record for loop-carried state plus a
    single-trip [_step] returning a small sum type, so a machine-level
    walk can index its loop invariant by trip count; [_wf] predicates
    collecting the caller obligations.  There are no [Admitted]s,
    [Axiom]s or [Parameter]s.

    THE CUT POINTS, and why they are these.  c5-invariants.md §3.5
    prescribes one CPS lemma per mode arm rather than one lemma for the
    whole [for(;;)], and this file exposes exactly that: [inf_HEAD],
    [inf_TYPEDO], ... are each a total function [InfCtx -> InfSt ->
    InfStep], [inf_step] is the [switch] that dispatches to them, and
    [inf_loop] is the [for(;;)].  A C [break] out of the switch is
    [InfCont]; a [goto inf_leave] is [InfLeave]; the three [return]s that
    bypass the epilogue are [InfRet].  Where the C FALLS THROUGH from one
    [case] to the next, the arm function CALLS the next arm function
    directly rather than setting the mode and returning [InfCont] — that
    is not cosmetic: [case TYPE] falls into [case TYPEDO] WITHOUT
    assigning [state->mode] ([:824-828]), and [inf_leave]'s [data_type]
    computation ([:1268]) can observe the difference.

    INTENDED TERMINATION MEASURE (not proved here; stated for the walk).
    §3.5's lexicographic pair: [(8 * br_have + br_bits) + o_left] strictly
    decreases on every arm that consumes input or produces output, and for
    the epsilon-transitions (the arms that only change [mode]) the
    mode rank orders the acyclic chains
    HEAD -> DICTID -> DICT -> TYPE -> TYPEDO -> {STORED, TABLE, LEN_} and
    TABLE -> LENLENS -> CODELENS -> LEN_ -> LEN and
    LEN -> LENEXT -> DIST -> DISTEXT -> MATCH and CHECK -> LENGTH -> DONE.
    [m_val] is the C enum's own numeric value, which is why it is
    tempting to use it as that rank -- it is literally the register
    comparison the compiled code performs at [:1259] and [:1261].

    BUT [m_val] IS NOT A MEASURE, and this header used to claim it was.
    [InflateThy.inf_rank_is_not_a_measure] exhibits a reachable
    [InfCont] across which it strictly INCREASES: [inflate.c:884-886],
    [case COPY] with [state->length = 0], sets [mode = TYPE] and touches
    neither the byte/bit budget nor [left], and
    [m_val COPY = 16195 > m_val TYPE = 16191].  It is reachable twice
    over -- an empty stored block, and the trip after an exactly-filled
    stored copy.  The C enum's order is simply not a topological order of
    the epsilon edges.  Use [InflateThy.inf_mrank] instead: the same
    [16180..16211] interval permuted so COPY_/COPY sink below TYPE, which
    is why [inf_fuel_dominates_rank] transfers to it verbatim
    ([InflateThy.inf_fuel_dominates_rank2]).

    Validated against the delivered binary: see
    [a working folder] (R1 boundary records from
    [/harness/reference_binary] under qemu GDB-RSP, plus an injected
    stress set). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
(* THE ONE LINE TO REPOINT when the lane lead's [ZBits.v] carries the
   inflate-side bit reader too. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** zlib return codes ([zlib.h:180-189]) and flush values ([:172-178])

    [Z_OK], [Z_STREAM_END], [Z_STREAM_ERROR], [Z_BUF_ERROR], [Z_NO_FLUSH],
    [Z_SYNC_FLUSH], [Z_FINISH], [Z_BLOCK] and [Z_DEFLATED] are shared with
    [Deflate.v] and are declared once in [Base.v] (see the integration note
    there); only the inflate-specific ones are declared here. *)

Definition Z_NEED_DICT     : Z := 2.
Definition Z_DATA_ERROR    : Z := -3.
Definition Z_MEM_ERROR     : Z := -4.
Definition Z_VERSION_ERROR : Z := -6.

Definition Z_TREES      : Z := 6.

(** [zlib.h:107] [#define DEF_WBITS MAX_WBITS] = 15 ([zconf.h:274]). *)
Definition DEF_WBITS : Z := 15.

(** ** The mode enum ([inflate.h:20-53])

    Represented as an inductive so the [switch] is a [match], with
    [m_val] giving the C enum's own numeric value so that the epilogue's
    [state->mode < BAD] / [< CHECK] comparisons ([inflate.c:1259],
    [:1261]) are the literal register comparisons. *)

Inductive Mode : Set :=
| M_HEAD  | M_FLAGS   | M_TIME     | M_OS   | M_EXLEN  | M_EXTRA
| M_NAME  | M_COMMENT | M_HCRC     | M_DICTID | M_DICT
| M_TYPE  | M_TYPEDO  | M_STORED   | M_COPY_ | M_COPY
| M_TABLE | M_LENLENS | M_CODELENS
| M_LEN_  | M_LEN     | M_LENEXT   | M_DIST | M_DISTEXT | M_MATCH | M_LIT
| M_CHECK | M_LENGTH  | M_DONE     | M_BAD  | M_MEM     | M_SYNC.

Definition m_val (m : Mode) : Z :=
  match m with
  | M_HEAD  => 16180 | M_FLAGS   => 16181 | M_TIME     => 16182
  | M_OS    => 16183 | M_EXLEN   => 16184 | M_EXTRA    => 16185
  | M_NAME  => 16186 | M_COMMENT => 16187 | M_HCRC     => 16188
  | M_DICTID=> 16189 | M_DICT    => 16190
  | M_TYPE  => 16191 | M_TYPEDO  => 16192 | M_STORED   => 16193
  | M_COPY_ => 16194 | M_COPY    => 16195 | M_TABLE    => 16196
  | M_LENLENS => 16197 | M_CODELENS => 16198
  | M_LEN_  => 16199 | M_LEN     => 16200 | M_LENEXT   => 16201
  | M_DIST  => 16202 | M_DISTEXT => 16203 | M_MATCH    => 16204
  | M_LIT   => 16205 | M_CHECK   => 16206 | M_LENGTH   => 16207
  | M_DONE  => 16208 | M_BAD     => 16209 | M_MEM      => 16210
  | M_SYNC  => 16211
  end.

(** ** Which table [lencode] / [distcode] point at

    The C stores a [code *].  It is either an offset into [state->codes]
    (every dynamic block) or the address of one of the two static tables
    [inffixed.h] provides (every fixed block).  [inflateResetKeep] sets
    both to [state->codes], i.e. [TRcodes 0] ([inflate.c:121]). *)

Inductive TblRef : Set :=
| TRcodes (off : Z)
| TRlenfix
| TRdistfix.

(** ** [inffixed.h] — the fixed-code tables

    [BUILDFIXED] is not defined ([materials/Makefile] passes no zlib
    defines), so [fixedtables] ([inflate.c:245-290]) hands out these
    literals rather than building them.  Transcribed verbatim from
    [materials/zlib-1.3.1/inffixed.h]; [lenfix_is_inflate_table] below
    ties them to [Inftrees.it_model], which is what [makefixed] used to
    generate them. *)
Definition lenfix_list : list (Z * Z * Z) :=
  [(96,7,0);(0,8,80);(0,8,16);(20,8,115);(18,7,31);(0,8,112)
  ;(0,8,48);(0,9,192);(16,7,10);(0,8,96);(0,8,32);(0,9,160)
  ;(0,8,0);(0,8,128);(0,8,64);(0,9,224);(16,7,6);(0,8,88)
  ;(0,8,24);(0,9,144);(19,7,59);(0,8,120);(0,8,56);(0,9,208)
  ;(17,7,17);(0,8,104);(0,8,40);(0,9,176);(0,8,8);(0,8,136)
  ;(0,8,72);(0,9,240);(16,7,4);(0,8,84);(0,8,20);(21,8,227)
  ;(19,7,43);(0,8,116);(0,8,52);(0,9,200);(17,7,13);(0,8,100)
  ;(0,8,36);(0,9,168);(0,8,4);(0,8,132);(0,8,68);(0,9,232)
  ;(16,7,8);(0,8,92);(0,8,28);(0,9,152);(20,7,83);(0,8,124)
  ;(0,8,60);(0,9,216);(18,7,23);(0,8,108);(0,8,44);(0,9,184)
  ;(0,8,12);(0,8,140);(0,8,76);(0,9,248);(16,7,3);(0,8,82)
  ;(0,8,18);(21,8,163);(19,7,35);(0,8,114);(0,8,50);(0,9,196)
  ;(17,7,11);(0,8,98);(0,8,34);(0,9,164);(0,8,2);(0,8,130)
  ;(0,8,66);(0,9,228);(16,7,7);(0,8,90);(0,8,26);(0,9,148)
  ;(20,7,67);(0,8,122);(0,8,58);(0,9,212);(18,7,19);(0,8,106)
  ;(0,8,42);(0,9,180);(0,8,10);(0,8,138);(0,8,74);(0,9,244)
  ;(16,7,5);(0,8,86);(0,8,22);(64,8,0);(19,7,51);(0,8,118)
  ;(0,8,54);(0,9,204);(17,7,15);(0,8,102);(0,8,38);(0,9,172)
  ;(0,8,6);(0,8,134);(0,8,70);(0,9,236);(16,7,9);(0,8,94)
  ;(0,8,30);(0,9,156);(20,7,99);(0,8,126);(0,8,62);(0,9,220)
  ;(18,7,27);(0,8,110);(0,8,46);(0,9,188);(0,8,14);(0,8,142)
  ;(0,8,78);(0,9,252);(96,7,0);(0,8,81);(0,8,17);(21,8,131)
  ;(18,7,31);(0,8,113);(0,8,49);(0,9,194);(16,7,10);(0,8,97)
  ;(0,8,33);(0,9,162);(0,8,1);(0,8,129);(0,8,65);(0,9,226)
  ;(16,7,6);(0,8,89);(0,8,25);(0,9,146);(19,7,59);(0,8,121)
  ;(0,8,57);(0,9,210);(17,7,17);(0,8,105);(0,8,41);(0,9,178)
  ;(0,8,9);(0,8,137);(0,8,73);(0,9,242);(16,7,4);(0,8,85)
  ;(0,8,21);(16,8,258);(19,7,43);(0,8,117);(0,8,53);(0,9,202)
  ;(17,7,13);(0,8,101);(0,8,37);(0,9,170);(0,8,5);(0,8,133)
  ;(0,8,69);(0,9,234);(16,7,8);(0,8,93);(0,8,29);(0,9,154)
  ;(20,7,83);(0,8,125);(0,8,61);(0,9,218);(18,7,23);(0,8,109)
  ;(0,8,45);(0,9,186);(0,8,13);(0,8,141);(0,8,77);(0,9,250)
  ;(16,7,3);(0,8,83);(0,8,19);(21,8,195);(19,7,35);(0,8,115)
  ;(0,8,51);(0,9,198);(17,7,11);(0,8,99);(0,8,35);(0,9,166)
  ;(0,8,3);(0,8,131);(0,8,67);(0,9,230);(16,7,7);(0,8,91)
  ;(0,8,27);(0,9,150);(20,7,67);(0,8,123);(0,8,59);(0,9,214)
  ;(18,7,19);(0,8,107);(0,8,43);(0,9,182);(0,8,11);(0,8,139)
  ;(0,8,75);(0,9,246);(16,7,5);(0,8,87);(0,8,23);(64,8,0)
  ;(19,7,51);(0,8,119);(0,8,55);(0,9,206);(17,7,15);(0,8,103)
  ;(0,8,39);(0,9,174);(0,8,7);(0,8,135);(0,8,71);(0,9,238)
  ;(16,7,9);(0,8,95);(0,8,31);(0,9,158);(20,7,99);(0,8,127)
  ;(0,8,63);(0,9,222);(18,7,27);(0,8,111);(0,8,47);(0,9,190)
  ;(0,8,15);(0,8,143);(0,8,79);(0,9,254);(96,7,0);(0,8,80)
  ;(0,8,16);(20,8,115);(18,7,31);(0,8,112);(0,8,48);(0,9,193)
  ;(16,7,10);(0,8,96);(0,8,32);(0,9,161);(0,8,0);(0,8,128)
  ;(0,8,64);(0,9,225);(16,7,6);(0,8,88);(0,8,24);(0,9,145)
  ;(19,7,59);(0,8,120);(0,8,56);(0,9,209);(17,7,17);(0,8,104)
  ;(0,8,40);(0,9,177);(0,8,8);(0,8,136);(0,8,72);(0,9,241)
  ;(16,7,4);(0,8,84);(0,8,20);(21,8,227);(19,7,43);(0,8,116)
  ;(0,8,52);(0,9,201);(17,7,13);(0,8,100);(0,8,36);(0,9,169)
  ;(0,8,4);(0,8,132);(0,8,68);(0,9,233);(16,7,8);(0,8,92)
  ;(0,8,28);(0,9,153);(20,7,83);(0,8,124);(0,8,60);(0,9,217)
  ;(18,7,23);(0,8,108);(0,8,44);(0,9,185);(0,8,12);(0,8,140)
  ;(0,8,76);(0,9,249);(16,7,3);(0,8,82);(0,8,18);(21,8,163)
  ;(19,7,35);(0,8,114);(0,8,50);(0,9,197);(17,7,11);(0,8,98)
  ;(0,8,34);(0,9,165);(0,8,2);(0,8,130);(0,8,66);(0,9,229)
  ;(16,7,7);(0,8,90);(0,8,26);(0,9,149);(20,7,67);(0,8,122)
  ;(0,8,58);(0,9,213);(18,7,19);(0,8,106);(0,8,42);(0,9,181)
  ;(0,8,10);(0,8,138);(0,8,74);(0,9,245);(16,7,5);(0,8,86)
  ;(0,8,22);(64,8,0);(19,7,51);(0,8,118);(0,8,54);(0,9,205)
  ;(17,7,15);(0,8,102);(0,8,38);(0,9,173);(0,8,6);(0,8,134)
  ;(0,8,70);(0,9,237);(16,7,9);(0,8,94);(0,8,30);(0,9,157)
  ;(20,7,99);(0,8,126);(0,8,62);(0,9,221);(18,7,27);(0,8,110)
  ;(0,8,46);(0,9,189);(0,8,14);(0,8,142);(0,8,78);(0,9,253)
  ;(96,7,0);(0,8,81);(0,8,17);(21,8,131);(18,7,31);(0,8,113)
  ;(0,8,49);(0,9,195);(16,7,10);(0,8,97);(0,8,33);(0,9,163)
  ;(0,8,1);(0,8,129);(0,8,65);(0,9,227);(16,7,6);(0,8,89)
  ;(0,8,25);(0,9,147);(19,7,59);(0,8,121);(0,8,57);(0,9,211)
  ;(17,7,17);(0,8,105);(0,8,41);(0,9,179);(0,8,9);(0,8,137)
  ;(0,8,73);(0,9,243);(16,7,4);(0,8,85);(0,8,21);(16,8,258)
  ;(19,7,43);(0,8,117);(0,8,53);(0,9,203);(17,7,13);(0,8,101)
  ;(0,8,37);(0,9,171);(0,8,5);(0,8,133);(0,8,69);(0,9,235)
  ;(16,7,8);(0,8,93);(0,8,29);(0,9,155);(20,7,83);(0,8,125)
  ;(0,8,61);(0,9,219);(18,7,23);(0,8,109);(0,8,45);(0,9,187)
  ;(0,8,13);(0,8,141);(0,8,77);(0,9,251);(16,7,3);(0,8,83)
  ;(0,8,19);(21,8,195);(19,7,35);(0,8,115);(0,8,51);(0,9,199)
  ;(17,7,11);(0,8,99);(0,8,35);(0,9,167);(0,8,3);(0,8,131)
  ;(0,8,67);(0,9,231);(16,7,7);(0,8,91);(0,8,27);(0,9,151)
  ;(20,7,67);(0,8,123);(0,8,59);(0,9,215);(18,7,19);(0,8,107)
  ;(0,8,43);(0,9,183);(0,8,11);(0,8,139);(0,8,75);(0,9,247)
  ;(16,7,5);(0,8,87);(0,8,23);(64,8,0);(19,7,51);(0,8,119)
  ;(0,8,55);(0,9,207);(17,7,15);(0,8,103);(0,8,39);(0,9,175)
  ;(0,8,7);(0,8,135);(0,8,71);(0,9,239);(16,7,9);(0,8,95)
  ;(0,8,31);(0,9,159);(20,7,99);(0,8,127);(0,8,63);(0,9,223)
  ;(18,7,27);(0,8,111);(0,8,47);(0,9,191);(0,8,15);(0,8,143)
  ;(0,8,79);(0,9,255)].

Definition distfix_list : list (Z * Z * Z) :=
  [(16,5,1);(23,5,257);(19,5,17);(27,5,4097);(17,5,5);(25,5,1025)
  ;(21,5,65);(29,5,16385);(16,5,3);(24,5,513);(20,5,33);(28,5,8193)
  ;(18,5,9);(26,5,2049);(22,5,129);(64,5,0);(16,5,2);(23,5,385)
  ;(19,5,25);(27,5,6145);(17,5,7);(25,5,1537);(21,5,97);(29,5,24577)
  ;(16,5,4);(24,5,769);(20,5,49);(28,5,12289);(18,5,13);(26,5,3073)
  ;(22,5,193);(64,5,0)].

Definition tbl_of_list (l : list (Z * Z * Z)) : ztbl :=
  fun i => let '(op, bits, val) := nth (Z.to_nat i) l (0, 0, 0) in mkCode op bits val.

Definition lenfix  : ztbl := tbl_of_list lenfix_list.
Definition distfix : ztbl := tbl_of_list distfix_list.

(** ** The output buffer

    [strm->next_out] as an index into a total array, plus [avail_out].
    Indices are absolute, so the C's [*(put - state->offset)] is a read at
    index [o_put - offset] and needs no separate base. *)
Record OB : Type := mkOB { o_buf : zarr; o_put : Z; o_left : Z }.

(** [*put++ = v; left--;] *)
Definition ob_write (o : OB) (v : Z) : OB :=
  {| o_buf := zset (o_buf o) (o_put o) v;
     o_put := o_put o + 1;
     o_left := o_left o - 1 |}.

(** The [n] bytes at index [i], as a list — what the ADLER/CRC update at
    [inflate.c:1198] and [:1265] is applied to. *)
Definition ob_slice (o : OB) (i n : Z) : list Z :=
  map (fun k => o_buf o (i + Z.of_nat k)) (seq 0 (Z.to_nat n)).

(** [zmemcpy(dst + di, src + si, n)] over total arrays. *)
Fixpoint zcopy (n : nat) (dst : zarr) (di : Z) (src : zarr) (si : Z) {struct n}
  : zarr :=
  match n with
  | O => dst
  | S k => zcopy k (zset dst di (src si)) (di + 1) src (si + 1)
  end.

(** [while (n--) a[i++] = v;] *)
Fixpoint zfill (n : nat) (a : zarr) (i v : Z) {struct n} : zarr :=
  match n with
  | O => a
  | S k => zfill k (zset a i v) (i + 1) v
  end.

(** MATCH's [from] ([inflate.c:1152-1163]) points either into
    [state->window] or into the output buffer, exactly as [inflate_fast]'s
    does; and as there, a copy from the output buffer must see its own
    earlier writes ([dist < len] run-length expansion), so the read is
    taken from the CURRENT [OB]. *)
Inductive OSrc : Set := OSwin (i : Z) | OSout (i : Z).

Definition os_read (win : zarr) (o : OB) (r : OSrc) : Z :=
  match r with OSwin i => win i | OSout i => o_buf o i end.

Definition os_bump (r : OSrc) : OSrc :=
  match r with OSwin i => OSwin (i + 1) | OSout i => OSout (i + 1) end.

Fixpoint ob_copyn (n : nat) (win : zarr) (o : OB) (r : OSrc) {struct n} : OB :=
  match n with
  | O => o
  | S k => ob_copyn k win (ob_write o (os_read win o r)) (os_bump r)
  end.

(** [zutil.h:251-252] [ZSWAP32]. *)
Definition zswap32 (q : Z) : Z :=
  Z.land (Z.shiftr q 24) 255 + Z.land (Z.shiftr q 8) 65280
  + Z.shiftl (Z.land q 65280) 8 + Z.shiftl (Z.land q 255) 24.

(** [inflate.c:416-421] [UPDATE_CHECK].  The CRC arm is gzip-only and
    therefore dead here ([flags] is 0 for a zlib stream, [:642]); its
    [align] argument is 0 because the answer does not depend on it —
    [Spec/PngModel/ChecksumThy.v]'s [crc32_z_at_align]. *)
Definition upd_check (flags check : Z) (bs : list Z) : Z :=
  if Z.eqb flags 0 then adler32_z check false bs else crc32_z check false 0 bs.

(** [inflate.c:504] [order[19]], the code-length code permutation. *)
Definition inf_order_l : list Z :=
  [16;17;18;0;8;7;9;6;10;5;11;4;12;3;13;2;14;1;15].
Definition inf_order : zarr := zlist inf_order_l.

(** ** [NEEDBITS] with the partial state kept

    The frozen [br_needbits] answers [None] on the [goto inf_leave] path,
    which loses the bytes the loop DID consume before the failing
    [PULLBYTE] — and the C keeps them ([hold], [bits], [next] and [have]
    are all updated in place by [PULLBYTE], and [RESTORE] then writes them
    to [strm]).  This wrapper keeps them; [inf_nb_needbits] below proves
    the two agree on the success path, so nothing here silently forks from
    the frozen interface.

    Fuel [Z.to_nat n]: every trip adds 8 to [bits], so at most
    [ceil(n/8) <= n] trips are needed for [n >= 1] and none for [n <= 0]. *)
Inductive NB : Type := NBOk (b : BR) | NBLeave (b : BR).

Fixpoint inf_nb_go (f : nat) (n : Z) (b : BR) {struct f} : NB :=
  match f with
  | O => if Z.ltb (br_bits b) n then NBLeave b else NBOk b
  | S k =>
      if Z.ltb (br_bits b) n
      then match br_pullbyte b with
           | None => NBLeave b
           | Some b' => inf_nb_go k n b'
           end
      else NBOk b
  end.

Definition inf_nb (n : Z) (b : BR) : NB := inf_nb_go (Z.to_nat n) n b.

(** ** The two code-fetch loops

    [inflate.c:1036-1040] / [:1085-1089] (root) and [:1043-1047] /
    [:1092-1096] (second level).  Both are
    [[for (;;) { here = tbl[...]; if (here.bits <= bits) break; PULLBYTE(); }]],
    i.e. "pull until the accumulator holds enough bits for the entry the
    accumulator selects".  Fuel [S (Z.to_nat (br_have b))]: every trip
    that recurses has just consumed one input byte, so the [O] case is
    unreachable — with an adversarial table the loop simply drains the
    input and takes the [goto inf_leave], which is what the C does. *)
Inductive Fetch : Type :=
| FetchOk (h : Code) (b : BR)
| FetchLeave (b : BR)
| FetchFuel.

Fixpoint inf_fetch_go (f : nat) (t : ztbl) (nb : Z) (b : BR) {struct f} : Fetch :=
  match f with
  | O => FetchFuel
  | S k =>
      let h := t (br_bits_of nb b) in
      if Z.leb (c_bits h) (br_bits b) then FetchOk h b
      else match br_pullbyte b with
           | None => FetchLeave b
           | Some b' => inf_fetch_go k t nb b'
           end
  end.

Definition inf_fetch (t : ztbl) (nb : Z) (b : BR) : Fetch :=
  inf_fetch_go (S (Z.to_nat (br_have b))) t nb b.

Fixpoint inf_fetch2_go (f : nat) (t : ztbl) (lst : Code) (b : BR) {struct f}
  : Fetch :=
  match f with
  | O => FetchFuel
  | S k =>
      let h := t (c_val lst
                  + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)) in
      if Z.leb (c_bits lst + c_bits h) (br_bits b) then FetchOk h b
      else match br_pullbyte b with
           | None => FetchLeave b
           | Some b' => inf_fetch2_go k t lst b'
           end
  end.

Definition inf_fetch2 (t : ztbl) (lst : Code) (b : BR) : Fetch :=
  inf_fetch2_go (S (Z.to_nat (br_have b))) t lst b.
Record IHdr : Type := mkIHdr {
  h_mode : Mode;
  h_last : Z;
  h_wrap : Z;
  h_havedict : Z;
  h_flags : Z;
  h_dmax : Z;
  h_check : Z;
  h_total : Z;
  h_head : Z
}.

Record IWin : Type := mkIWin {
  w_wbits : Z;
  w_wsize : Z;
  w_whave : Z;
  w_wnext : Z;
  w_alloc : bool;
  w_win : zarr
}.

Record ICur : Type := mkICur {
  u_length : Z;
  u_offset : Z;
  u_extra : Z;
  u_back : Z;
  u_was : Z
}.

Record ITab : Type := mkITab {
  t_lencode : TblRef;
  t_distcode : TblRef;
  t_lenbits : Z;
  t_distbits : Z;
  t_next : Z;
  t_codes : ztbl;
  t_sane : Z
}.

Record IBld : Type := mkIBld {
  b_ncode : Z;
  b_nlen : Z;
  b_ndist : Z;
  b_have : Z;
  b_lens : zarr;
  b_work : zarr
}.

Record IState : Type := mkIState {
  s_hdr : IHdr;
  s_win : IWin;
  s_cur : ICur;
  s_tab : ITab;
  s_bld : IBld;
  s_hold : Z;
  s_bits : Z
}.

(** Field setters.  Rocq has no record-update syntax, so each write the C
    performs gets a one-line setter; the arms below then read like the C's
    statement sequence.  Mechanically generated, and each one rebuilds only
    its own cluster. *)

Definition set_mode (s : IState) (v : Mode) : IState :=
  let x := s_hdr s in let y := mkIHdr v (h_last x) (h_wrap x) (h_havedict x) (h_flags x) (h_dmax x) (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_last (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) v (h_wrap x) (h_havedict x) (h_flags x) (h_dmax x) (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_wrap (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) v (h_havedict x) (h_flags x) (h_dmax x) (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_havedict (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) v (h_flags x) (h_dmax x) (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_flags (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) (h_havedict x) v (h_dmax x) (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_dmax (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) (h_havedict x) (h_flags x) v (h_check x) (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_check (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) (h_havedict x) (h_flags x) (h_dmax x) v (h_total x) (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_total (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) (h_havedict x) (h_flags x) (h_dmax x) (h_check x) v (h_head x) in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_head (s : IState) (v : Z) : IState :=
  let x := s_hdr s in let y := mkIHdr (h_mode x) (h_last x) (h_wrap x) (h_havedict x) (h_flags x) (h_dmax x) (h_check x) (h_total x) v in
  mkIState y (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_wbits (s : IState) (v : Z) : IState :=
  let x := s_win s in let y := mkIWin v (w_wsize x) (w_whave x) (w_wnext x) (w_alloc x) (w_win x) in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_wsize (s : IState) (v : Z) : IState :=
  let x := s_win s in let y := mkIWin (w_wbits x) v (w_whave x) (w_wnext x) (w_alloc x) (w_win x) in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_whave (s : IState) (v : Z) : IState :=
  let x := s_win s in let y := mkIWin (w_wbits x) (w_wsize x) v (w_wnext x) (w_alloc x) (w_win x) in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_wnext (s : IState) (v : Z) : IState :=
  let x := s_win s in let y := mkIWin (w_wbits x) (w_wsize x) (w_whave x) v (w_alloc x) (w_win x) in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_alloc (s : IState) (v : bool) : IState :=
  let x := s_win s in let y := mkIWin (w_wbits x) (w_wsize x) (w_whave x) (w_wnext x) v (w_win x) in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_win (s : IState) (v : zarr) : IState :=
  let x := s_win s in let y := mkIWin (w_wbits x) (w_wsize x) (w_whave x) (w_wnext x) (w_alloc x) v in
  mkIState (s_hdr s) y (s_cur s) (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_length (s : IState) (v : Z) : IState :=
  let x := s_cur s in let y := mkICur v (u_offset x) (u_extra x) (u_back x) (u_was x) in
  mkIState (s_hdr s) (s_win s) y (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_offset (s : IState) (v : Z) : IState :=
  let x := s_cur s in let y := mkICur (u_length x) v (u_extra x) (u_back x) (u_was x) in
  mkIState (s_hdr s) (s_win s) y (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_extra (s : IState) (v : Z) : IState :=
  let x := s_cur s in let y := mkICur (u_length x) (u_offset x) v (u_back x) (u_was x) in
  mkIState (s_hdr s) (s_win s) y (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_back (s : IState) (v : Z) : IState :=
  let x := s_cur s in let y := mkICur (u_length x) (u_offset x) (u_extra x) v (u_was x) in
  mkIState (s_hdr s) (s_win s) y (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_was (s : IState) (v : Z) : IState :=
  let x := s_cur s in let y := mkICur (u_length x) (u_offset x) (u_extra x) (u_back x) v in
  mkIState (s_hdr s) (s_win s) y (s_tab s) (s_bld s) (s_hold s) (s_bits s).

Definition set_lencode (s : IState) (v : TblRef) : IState :=
  let x := s_tab s in let y := mkITab v (t_distcode x) (t_lenbits x) (t_distbits x) (t_next x) (t_codes x) (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_distcode (s : IState) (v : TblRef) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) v (t_lenbits x) (t_distbits x) (t_next x) (t_codes x) (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_lenbits (s : IState) (v : Z) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) (t_distcode x) v (t_distbits x) (t_next x) (t_codes x) (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_distbits (s : IState) (v : Z) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) (t_distcode x) (t_lenbits x) v (t_next x) (t_codes x) (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_next (s : IState) (v : Z) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) (t_distcode x) (t_lenbits x) (t_distbits x) v (t_codes x) (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_codes (s : IState) (v : ztbl) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) (t_distcode x) (t_lenbits x) (t_distbits x) (t_next x) v (t_sane x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_sane (s : IState) (v : Z) : IState :=
  let x := s_tab s in let y := mkITab (t_lencode x) (t_distcode x) (t_lenbits x) (t_distbits x) (t_next x) (t_codes x) v in
  mkIState (s_hdr s) (s_win s) (s_cur s) y (s_bld s) (s_hold s) (s_bits s).

Definition set_ncode (s : IState) (v : Z) : IState :=
  let x := s_bld s in let y := mkIBld v (b_nlen x) (b_ndist x) (b_have x) (b_lens x) (b_work x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_nlen (s : IState) (v : Z) : IState :=
  let x := s_bld s in let y := mkIBld (b_ncode x) v (b_ndist x) (b_have x) (b_lens x) (b_work x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_ndist (s : IState) (v : Z) : IState :=
  let x := s_bld s in let y := mkIBld (b_ncode x) (b_nlen x) v (b_have x) (b_lens x) (b_work x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_have (s : IState) (v : Z) : IState :=
  let x := s_bld s in let y := mkIBld (b_ncode x) (b_nlen x) (b_ndist x) v (b_lens x) (b_work x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_lens (s : IState) (v : zarr) : IState :=
  let x := s_bld s in let y := mkIBld (b_ncode x) (b_nlen x) (b_ndist x) (b_have x) v (b_work x) in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_work (s : IState) (v : zarr) : IState :=
  let x := s_bld s in let y := mkIBld (b_ncode x) (b_nlen x) (b_ndist x) (b_have x) (b_lens x) v in
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) y (s_hold s) (s_bits s).

Definition set_hold (s : IState) (v : Z) : IState :=
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) (s_bld s) v (s_bits s).

Definition set_bits (s : IState) (v : Z) : IState :=
  mkIState (s_hdr s) (s_win s) (s_cur s) (s_tab s) (s_bld s) (s_hold s) v.
(** The [z_stream] fields that survive across an [inflate] call and are
    not held in a C local: [total_in], [total_out], [adler], [data_type],
    [msg].  [next_in]/[avail_in] live in the [BR] and
    [next_out]/[avail_out] in the [OB], because [LOAD]/[RESTORE]
    ([inflate.c:441-457]) keep exactly those four in locals for the whole
    body; the model never separates the two copies, so [RESTORE] is a
    no-op on them and only [q_restore]'s [hold]/[bits] write remains. *)
Record Strm : Type := mkStrm {
  z_tin : Z;
  z_tout : Z;
  z_adler : Z;
  z_dtype : Z;
  z_msg : Z
}.

Definition zset_tin (z : Strm) (v : Z) : Strm := mkStrm v (z_tout z) (z_adler z) (z_dtype z) (z_msg z).
Definition zset_tout (z : Strm) (v : Z) : Strm := mkStrm (z_tin z) v (z_adler z) (z_dtype z) (z_msg z).
Definition zset_adler (z : Strm) (v : Z) : Strm := mkStrm (z_tin z) (z_tout z) v (z_dtype z) (z_msg z).
Definition zset_dtype (z : Strm) (v : Z) : Strm := mkStrm (z_tin z) (z_tout z) (z_adler z) v (z_msg z).
Definition zset_msg (z : Strm) (v : Z) : Strm := mkStrm (z_tin z) (z_tout z) (z_adler z) (z_dtype z) v.

(** The whole machine state of one [inflate] call: the [inflate_state],
    the surviving [z_stream] fields, and the C locals
    [next]/[have]/[hold]/[bits] (the [BR]), [put]/[left] (the [OB]),
    [in], [out] and [ret] ([inflate.c:585-598]). *)
Record InfSt : Type := mkInfSt {
  q_st : IState;
  q_z : Strm;
  q_br : BR;
  q_ob : OB;
  q_in : Z;
  q_out : Z;
  q_ret : Z
}.

Definition qset_st (q : InfSt) (v : IState) : InfSt := mkInfSt v (q_z q) (q_br q) (q_ob q) (q_in q) (q_out q) (q_ret q).
Definition qset_z (q : InfSt) (v : Strm) : InfSt := mkInfSt (q_st q) v (q_br q) (q_ob q) (q_in q) (q_out q) (q_ret q).
Definition qset_br (q : InfSt) (v : BR) : InfSt := mkInfSt (q_st q) (q_z q) v (q_ob q) (q_in q) (q_out q) (q_ret q).
Definition qset_ob (q : InfSt) (v : OB) : InfSt := mkInfSt (q_st q) (q_z q) (q_br q) v (q_in q) (q_out q) (q_ret q).
Definition qset_in (q : InfSt) (v : Z) : InfSt := mkInfSt (q_st q) (q_z q) (q_br q) (q_ob q) v (q_out q) (q_ret q).
Definition qset_out (q : InfSt) (v : Z) : InfSt := mkInfSt (q_st q) (q_z q) (q_br q) (q_ob q) (q_in q) v (q_ret q).
Definition qset_ret (q : InfSt) (v : Z) : InfSt := mkInfSt (q_st q) (q_z q) (q_br q) (q_ob q) (q_in q) (q_out q) v.

(** Resolve a [code *] to the table it denotes. *)
Definition tbl_of (s : IState) (r : TblRef) : ztbl :=
  match r with
  | TRcodes k => fun i => t_codes (s_tab s) (k + i)
  | TRlenfix  => lenfix
  | TRdistfix => distfix
  end.

(** Write an [inflate_table] result back into [state->codes] at the offset
    the C's [*table] pointer had.  [it_model] indexes its output table
    from [*table], so the shift is exactly the C's pointer arithmetic;
    indices below [k] are untouched, and [it_model] never writes a
    negative index. *)
Definition codes_wb (cs : ztbl) (k : Z) (t : ztbl) : ztbl :=
  fun i => if Z.leb k i then t (i - k) else cs i.

(** ** [updatewindow] — [inflate.c:365-412]

    [alloc] says whether the [ZALLOC] at [:375-377] succeeds and [fresh]
    what it hands back; per the campaign's call-boundary convention the
    allocation is a PARAMETER of the model, not a simulated allocator.
    The fresh bytes are never read below [whave], which starts at 0.
    [None] is the C's [return 1] (out of memory). *)
Definition uw (alloc : bool) (fresh : zarr) (s : IState) (o : OB) (copy : Z)
  : option IState :=
  let wn := s_win s in
  match (if w_alloc wn then Some (w_win wn)
         else if alloc then Some fresh else None) with
  | None => None                                       (* :378 [return 1] *)
  | Some win0 =>
      let s1 := set_win (set_alloc s true) win0 in
      (* :382-386: [if (state->wsize == 0) { wsize = 1U << wbits; wnext = 0;
         whave = 0; }] *)
      let wsz := if Z.eqb (w_wsize wn) 0 then Z.shiftl 1 (w_wbits wn)
                 else w_wsize wn in
      let wnx := if Z.eqb (w_wsize wn) 0 then 0 else w_wnext wn in
      let whv := if Z.eqb (w_wsize wn) 0 then 0 else w_whave wn in
      let e   := o_put o in                            (* [end] = strm->next_out *)
      if Z.leb wsz copy then
        (* :389-393 *)
        Some (set_whave (set_wnext (set_wsize
                (set_win s1 (zcopy (Z.to_nat wsz) win0 0 (o_buf o) (e - wsz)))
                wsz) 0) wsz)
      else
        (* :395-411 *)
        let d0   := wsz - wnx in
        let dist := if Z.ltb copy d0 then copy else d0 in
        let win1 := zcopy (Z.to_nat dist) win0 wnx (o_buf o) (e - copy) in
        let cp1  := u32 (copy - dist) in
        if negb (Z.eqb cp1 0) then
          (* :400-404 *)
          Some (set_whave (set_wnext (set_wsize
                  (set_win s1 (zcopy (Z.to_nat cp1) win1 0 (o_buf o) (e - cp1)))
                  wsz) cp1) wsz)
        else
          (* :406-410 *)
          let w1 := wnx + dist in
          let w2 := if Z.eqb w1 wsz then 0 else w1 in
          let h1 := if Z.ltb whv wsz then whv + dist else whv in
          Some (set_whave (set_wnext (set_wsize (set_win s1 win1) wsz) w2) h1)
  end.

(** ** The call context

    Everything an [inflate] call is parameterised by that is not state:
    the [flush] argument, and the window allocation the first
    [updatewindow] may need. *)
Record InfCtx : Type := mkInfCtx {
  n_flush  : Z;
  n_walloc : bool;   (** does the [ZALLOC] at [inflate.c:376] succeed? *)
  n_wfresh : zarr    (** and what does it hand back (never read below whave) *)
}.

(** What one trip of the [for (;;) switch] does.

    [InfCont] is a C [break] out of the [switch] (the [for(;;)] then
    re-dispatches), [InfLeave] a [goto inf_leave], and [InfRet] one of the
    three [return]s that bypass the epilogue entirely — DICT's
    [Z_NEED_DICT] ([:817]) does [RESTORE()] first, MEM's [Z_MEM_ERROR]
    ([:1236]) and SYNC/[default]'s [Z_STREAM_ERROR] ([:1239]) do not.
    [InfDead] marked the eight gzip arms until the 2026-08-19 zlib-rt
    transcription; it is retained for interface stability but no longer
    produced.  [InfFuel] marks a fuel bound that [inf_wf] rules out. *)
Inductive InfStep : Type :=
| InfCont  (q : InfSt)
| InfLeave (q : InfSt)
| InfRet   (q : InfSt) (r : Z)
| InfDead  (m : Mode)
| InfFuel.

(** ** Small state moves shared by the arms *)

Definition q_mode (q : InfSt) : Mode := h_mode (s_hdr (q_st q)).

Definition qmode (q : InfSt) (m : Mode) : InfSt :=
  qset_st q (set_mode (q_st q) m).

(** [strm->msg = "..."; state->mode = BAD;] — fifteen sites. *)
Definition qbad (q : InfSt) (m : Z) : InfSt :=
  qmode (qset_z q (zset_msg (q_z q) m)) M_BAD.

(** [inflate.c:449-457] [RESTORE()].  [next]/[have]/[put]/[left] are not
    duplicated in this model, so all that is left is the [hold]/[bits]
    write-back into the struct. *)
Definition q_restore (q : InfSt) : InfSt :=
  qset_st q (set_bits (set_hold (q_st q) (br_hold (q_br q)))
                      (br_bits (q_br q))).

(** [inflate.c:441-447] [LOAD()], likewise. *)
Definition q_load (q : InfSt) : InfSt :=
  let b := q_br q in
  qset_br q {| br_in := br_in b; br_have := br_have b; br_next := br_next b;
               br_hold := s_hold (q_st q); br_bits := s_bits (q_st q) |}.

(** [strm->adler = state->check = v] — the pair that always moves
    together ([:641], [:811], [:820], [:1198]). *)
Definition qcheck (q : InfSt) (v : Z) : InfSt :=
  qset_z (qset_st q (set_check (q_st q) v)) (zset_adler (q_z q) v).

(** ** The mode arms

    One total function per [case], in reverse fallthrough order so that a
    [case] that falls into the next one can CALL it (see the header on why
    that, and not "assign the mode and re-dispatch"). *)

(** [inflate.c:1235-1236] [case MEM]: [return Z_MEM_ERROR] with no
    [RESTORE]. *)
Definition inf_MEM (q : InfSt) : InfStep := InfRet q Z_MEM_ERROR.

(** [inflate.c:1237-1240] [case SYNC] / [default]: [return Z_STREAM_ERROR]
    with no [RESTORE].  Unreachable: [inflateSync] is never called and
    [mode] always holds one of the enum's values. *)
Definition inf_SYNC (q : InfSt) : InfStep := InfRet q Z_STREAM_ERROR.

(** [inflate.c:1232-1234] [case BAD]. *)
Definition inf_BAD (q : InfSt) : InfStep := InfLeave (qset_ret q Z_DATA_ERROR).

(** [inflate.c:1229-1231] [case DONE]. *)
Definition inf_DONE (q : InfSt) : InfStep := InfLeave (qset_ret q Z_STREAM_END).

(** [inflate.c:1206-1228] [case LENGTH], falling through to DONE.  The
    body is gated on [state->wrap && state->flags] and [flags] is 0 for a
    zlib stream, so for this driver only the fallthrough executes. *)
Definition inf_LENGTH (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  if negb (Z.eqb (h_wrap h) 0) && negb (Z.eqb (h_flags h) 0) then
    match inf_nb 32 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        if negb (Z.eqb (Z.land (h_wrap h) 4) 0)
           && negb (Z.eqb (br_hold b) (Z.land (h_total h) 4294967295)) then
          (* :1213-1216 *)
          InfCont (qbad (qset_br q b) MSG_LENGTH_CHECK)
        else
          inf_DONE (qmode (qset_br q (br_initbits b)) M_DONE)
    end
  else inf_DONE (qmode q M_DONE).

(** [inflate.c:1188-1205] [case CHECK], falling through to LENGTH.

    [out] is doing double duty here: [out -= left] turns the entry
    snapshot into "bytes written this call", they are folded into the
    running totals and the check value, and then [out = left] restarts the
    snapshot so [inf_leave] does not count them twice. *)
Definition inf_CHECK (q : InfSt) : InfStep :=
  let st := q_st q in
  let h  := s_hdr st in
  if Z.eqb (h_wrap h) 0 then inf_LENGTH (qmode q M_LENGTH)
  else
    match inf_nb 32 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        let o    := q_ob q in
        let wrote := q_out q - o_left o in                    (* :1191 *)
        let q1 := qset_br q b in
        let q2 := qset_z q1 (zset_tout (q_z q1) (z_tout (q_z q1) + wrote)) in
        let q3 := qset_st q2 (set_total (q_st q2) (h_total h + wrote)) in
        let q4 := if negb (Z.eqb (Z.land (h_wrap h) 4) 0) && negb (Z.eqb wrote 0)
                  then qcheck q3 (upd_check (h_flags h) (h_check h)
                                            (ob_slice o (o_put o - wrote) wrote))
                  else q3 in
        let q5 := qset_out q4 (o_left o) in                   (* :1199 *)
        let ck := h_check (s_hdr (q_st q5)) in
        if negb (Z.eqb (Z.land (h_wrap h) 4) 0)
           && negb (Z.eqb (if Z.eqb (h_flags h) 0 then zswap32 (br_hold b)
                           else br_hold b) ck) then
          (* :1202-1205 *)
          InfCont (qbad q5 MSG_DATA_CHECK)
        else
          inf_LENGTH (qmode (qset_br q5 (br_initbits b)) M_LENGTH)
    end.

(** [inflate.c:1181-1187] [case LIT]. *)
Definition inf_LIT (q : InfSt) : InfStep :=
  if Z.eqb (o_left (q_ob q)) 0 then InfLeave q
  else
    let len := u_length (s_cur (q_st q)) in
    InfCont (qmode (qset_ob q (ob_write (q_ob q) (u8 len))) M_LEN).

(** [inflate.c:1129-1180] [case MATCH].

    The [do { *put++ = *from++; } while (--copy);] at [:1174-1176] runs
    with [copy >= 1] on every reachable path: [left != 0] was just tested,
    [state->length >= 1] (MATCH is entered from DISTEXT with a length code
    base of at least 3, and the arm sets [mode = LEN] as soon as [length]
    hits 0), and the window branch takes [copy = min(copy, length, left)]
    of three positive quantities.  So [ob_copyn (Z.to_nat copy)] is
    faithful; [inf_wf] records the obligation.

    The [INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR] arm at [:1138-1150]
    is compiled out, leaving [if (copy > whave) { if (sane) {...} }] with
    an empty else — so [sane = 0] would fall through into the window read.
    Dead ([sane] is 1) and transcribed. *)
Definition inf_MATCH (q : InfSt) : InfStep :=
  let st := q_st q in
  let o  := q_ob q in
  let wn := s_win st in
  let cu := s_cur st in
  if Z.eqb (o_left o) 0 then InfLeave q
  else
    let outd := u32 (q_out q - o_left o) in               (* :1131 *)
    if Z.ltb outd (u_offset cu) then
      (* :1132-1170 copy from the window *)
      let cw := u32 (u_offset cu - outd) in
      if Z.ltb (w_whave wn) cw && negb (Z.eqb (t_sane (s_tab st)) 0) then
        InfCont (qbad q MSG_DIST_FAR)
      else
        let '(cw1, src) :=
          if Z.ltb (w_wnext wn) cw
          then let c1 := u32 (cw - w_wnext wn) in
               (c1, OSwin (w_wsize wn - c1))              (* :1160-1162 *)
          else (cw, OSwin (w_wnext wn - cw)) in           (* :1164 *)
        let cw2 := if Z.ltb (u_length cu) cw1 then u_length cu else cw1 in
        let cw3 := if Z.ltb (o_left o) cw2 then o_left o else cw2 in
        let o'  := ob_copyn (Z.to_nat cw3) (w_win wn) o src in
        let st' := set_length st (u32 (u_length cu - cw3)) in
        let q'  := qset_ob (qset_st q st') o' in
        InfCont (if Z.eqb (u_length cu - cw3) 0 then qmode q' M_LEN else q')
    else
      (* :1171-1174 copy direct from the output *)
      let src := OSout (o_put o - u_offset cu) in
      let cw3 := if Z.ltb (o_left o) (u_length cu) then o_left o else u_length cu in
      let o'  := ob_copyn (Z.to_nat cw3) (w_win wn) o src in
      let st' := set_length st (u32 (u_length cu - cw3)) in
      let q'  := qset_ob (qset_st q st') o' in
      InfCont (if Z.eqb (u_length cu - cw3) 0 then qmode q' M_LEN else q').

(** [inflate.c:1113-1128] [case DISTEXT], falling through to MATCH.  The
    [INFLATE_STRICT] [offset > dmax] rejection at [:1121-1127] is compiled
    out. *)
Definition inf_DISTEXT (q : InfSt) : InfStep :=
  let cu := s_cur (q_st q) in
  if Z.eqb (u_extra cu) 0 then inf_MATCH (qmode q M_MATCH)
  else
    match inf_nb (u_extra cu) (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        let st1 := set_offset (q_st q) (u_offset cu + br_bits_of (u_extra cu) b) in
        let st2 := set_back st1 (u_back cu + u_extra cu) in
        inf_MATCH (qmode (qset_br (qset_st q st2) (br_dropbits (u_extra cu) b))
                         M_MATCH)
    end.

(** ** The two-level table decode

    Shared by LEN ([inflate.c:1036-1052]) and DIST ([:1085-1101]), which
    differ only in the guard that decides whether the root entry is a
    sub-table pointer: LEN tests [here.op && (here.op & 0xf0) == 0]
    ([:1041]), DIST tests [(here.op & 0xf0) == 0] with no [here.op &&]
    ([:1090]).  Both then [DROPBITS] the parent's bits and the entry's,
    adding both to [state->back].  [nb] is that total. *)
Inductive Dec : Type :=
| DecOk    (h : Code) (b : BR) (nb : Z)
| DecLeave (b : BR)
| DecFuel.

Definition inf_decode (sub : Code -> bool) (t : ztbl) (rootbits : Z) (b : BR)
  : Dec :=
  match inf_fetch t rootbits b with
  | FetchFuel     => DecFuel
  | FetchLeave b' => DecLeave b'
  | FetchOk h0 b0 =>
      if sub h0 then
        match inf_fetch2 t h0 b0 with
        | FetchFuel     => DecFuel
        | FetchLeave b' => DecLeave b'
        | FetchOk h1 b1 =>
            let b2 := br_dropbits (c_bits h0) b1 in
            DecOk h1 (br_dropbits (c_bits h1) b2) (c_bits h0 + c_bits h1)
        end
      else DecOk h0 (br_dropbits (c_bits h0) b0) (c_bits h0)
  end.

Definition sub_len  (h : Code) : bool :=
  negb (Z.eqb (c_op h) 0) && Z.eqb (Z.land (c_op h) 240) 0.
Definition sub_dist (h : Code) : bool := Z.eqb (Z.land (c_op h) 240) 0.

(** [inflate.c:1084-1112] [case DIST], falling through to DISTEXT. *)
Definition inf_DIST (q : InfSt) : InfStep :=
  let st := q_st q in
  let tb := s_tab st in
  match inf_decode sub_dist (tbl_of st (t_distcode tb)) (t_distbits tb) (q_br q) with
  | DecFuel      => InfFuel
  | DecLeave b   => InfLeave (qset_br q b)
  | DecOk h b nb =>
      let q1 := qset_br (qset_st q (set_back st (u_back (s_cur st) + nb))) b in
      if negb (Z.eqb (Z.land (c_op h) 64) 0) then
        (* :1103-1106 *)
        InfCont (qbad q1 MSG_DIST_CODE)
      else
        let st1 := set_extra (set_offset (q_st q1) (c_val h)) (Z.land (c_op h) 15) in
        inf_DISTEXT (qmode (qset_st q1 st1) M_DISTEXT)
  end.

(** [inflate.c:1073-1083] [case LENEXT], falling through to DIST. *)
Definition inf_LENEXT (q : InfSt) : InfStep :=
  let cu := s_cur (q_st q) in
  match (if Z.eqb (u_extra cu) 0 then NBOk (q_br q)
         else inf_nb (u_extra cu) (q_br q)) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let '(st1, b1) :=
        if Z.eqb (u_extra cu) 0 then (q_st q, b)
        else (set_back (set_length (q_st q)
                          (u_length cu + br_bits_of (u_extra cu) b))
                       (u_back cu + u_extra cu),
              br_dropbits (u_extra cu) b) in
      let st2 := set_was st1 (u_length (s_cur st1)) in
      inf_DIST (qmode (qset_br (qset_st q st2) b1) M_DIST)
  end.

(** [inflate.c:1025-1072] [case LEN], falling through to LENEXT.

    The [inflate_fast] fast path at [:1026-1033] is an ordinary call node:
    [RESTORE()], the call, [LOAD()].  [start] is the C's [out] local. *)
Definition inf_LEN (q : InfSt) : InfStep :=
  let st := q_st q in
  let tb := s_tab st in
  let b  := q_br q in
  let o  := q_ob q in
  if Z.leb 6 (br_have b) && Z.leb 258 (o_left o) then
    let q0 := q_restore q in
    match if_model {| a_inbuf     := br_in b;
                      a_next_in   := br_next b;
                      a_avail_in  := br_have b;
                      a_buf       := o_buf o;
                      a_next_out  := o_put o;
                      a_avail_out := o_left o;
                      a_start     := q_out q;
                      a_wsize     := w_wsize (s_win st);
                      a_whave     := w_whave (s_win st);
                      a_wnext     := w_wnext (s_win st);
                      a_window    := w_win (s_win st);
                      a_lcode     := tbl_of st (t_lencode tb);
                      a_dcode     := tbl_of st (t_distcode tb);
                      a_lenbits   := t_lenbits tb;
                      a_distbits  := t_distbits tb;
                      a_sane      := t_sane tb;
                      a_hold      := s_hold (q_st q0);
                      a_bits      := s_bits (q_st q0) |} with
    | None => InfFuel
    | Some y =>
        (* [inflate_fast] writes back [next_in]/[avail_in]/[next_out]/
           [avail_out]/[hold]/[bits] and, on an exit other than LEN,
           [state->mode] and [strm->msg] ([inffast.c:276-283]). *)
        let st1 := set_bits (set_hold (q_st q0) (y_hold y)) (y_bits y) in
        let q1  := qset_st q0 st1 in
        let q2  := qset_br q1 {| br_in := br_in b; br_have := y_avail_in y;
                                 br_next := y_in y;
                                 br_hold := br_hold b; br_bits := br_bits b |} in
        let q3  := qset_ob q2 {| o_buf := y_buf y; o_put := y_out y;
                                 o_left := y_avail_out y |} in
        let q4  := match y_exit y with
                   | ExLen    => q3
                   | ExType   => qmode q3 M_TYPE
                   | ExBad m  => qbad q3 m
                   end in
        (* [LOAD()] at [:1030] *)
        let q5 := q_load q4 in
        (* :1031-1032 *)
        InfCont (match q_mode q5 with
                 | M_TYPE => qset_st q5 (set_back (q_st q5) (-1))
                 | _ => q5
                 end)
    end
  else
    let q0 := qset_st q (set_back st 0) in                     (* :1034 *)
    match inf_decode sub_len (tbl_of st (t_lencode tb)) (t_lenbits tb) b with
    | DecFuel      => InfFuel
    | DecLeave b'  => InfLeave (qset_br q0 b')
    | DecOk h b' nb =>
        let st1 := set_length (set_back (q_st q0) (0 + nb)) (c_val h) in
        let q1  := qset_br (qset_st q0 st1) b' in
        if Z.eqb (c_op h) 0 then
          (* :1053-1058 literal *)
          InfCont (qmode q1 M_LIT)
        else if negb (Z.eqb (Z.land (c_op h) 32) 0) then
          (* :1059-1064 end of block *)
          InfCont (qmode (qset_st q1 (set_back (q_st q1) (-1))) M_TYPE)
        else if negb (Z.eqb (Z.land (c_op h) 64) 0) then
          (* :1065-1069 *)
          InfCont (qbad q1 MSG_LIT_LEN_CODE)
        else
          let st2 := set_extra (q_st q1) (Z.land (c_op h) 15) in
          inf_LENEXT (qmode (qset_st q1 st2) M_LENEXT)
    end.

(** [inflate.c:1023-1024] [case LEN_], falling through to LEN. *)
Definition inf_LEN_ (q : InfSt) : InfStep := inf_LEN (qmode q M_LEN).

(** ** CODELENS's inner [while] — [inflate.c:935-985]

    One trip per code-length symbol decoded, which is the granularity a
    machine-level loop invariant wants.  [tot] is [nlen + ndist], at most
    [286 + 30 = 316 < 320], so the writes into [lens[320]] stay in range
    (TABLE's check at [:900] is what guarantees that; [inf_wf] records
    it). *)
Record ClSt : Type := mkClSt { cl_have : Z; cl_lens : zarr; cl_br : BR }.

Inductive ClStep : Type :=
| ClCont  (s : ClSt)
| ClDone  (s : ClSt)          (** the [while] condition went false *)
| ClBad   (s : ClSt) (m : Z)  (** [break] out of the [while], [mode := BAD] *)
| ClLeave (s : ClSt)          (** [goto inf_leave] *)
| ClFuel.

Definition cl_step (t : ztbl) (nb tot : Z) (s : ClSt) : ClStep :=
  if Z.leb tot (cl_have s) then ClDone s
  else
    match inf_fetch t nb (cl_br s) with
    | FetchFuel    => ClFuel
    | FetchLeave b => ClLeave {| cl_have := cl_have s; cl_lens := cl_lens s;
                                 cl_br := b |}
    | FetchOk h b =>
        if Z.ltb (c_val h) 16 then
          (* :941-944 *)
          ClCont {| cl_have := cl_have s + 1;
                    cl_lens := zset (cl_lens s) (cl_have s) (c_val h);
                    cl_br   := br_dropbits (c_bits h) b |}
        else
          (* :946-971: NEEDBITS first, then DROPBITS(here.bits) *)
          let need := if Z.eqb (c_val h) 16 then c_bits h + 2
                      else if Z.eqb (c_val h) 17 then c_bits h + 3
                      else c_bits h + 7 in
          match inf_nb need b with
          | NBLeave b' => ClLeave {| cl_have := cl_have s; cl_lens := cl_lens s;
                                     cl_br := b' |}
          | NBOk b' =>
              let b1 := br_dropbits (c_bits h) b' in
              let r :=
                if Z.eqb (c_val h) 16 then
                  (* :948-957 *)
                  if Z.eqb (cl_have s) 0 then None
                  else Some (cl_lens s (cl_have s - 1), 3 + br_bits_of 2 b1,
                             br_dropbits 2 b1)
                else if Z.eqb (c_val h) 17 then
                  (* :958-964 *)
                  Some (0, 3 + br_bits_of 3 b1, br_dropbits 3 b1)
                else
                  (* :965-971 *)
                  Some (0, 11 + br_bits_of 7 b1, br_dropbits 7 b1) in
              match r with
              | None =>
                  ClBad {| cl_have := cl_have s; cl_lens := cl_lens s;
                           cl_br := b1 |} MSG_BL_REPEAT
              | Some (len, cp, b2) =>
                  if Z.ltb tot (cl_have s + cp) then
                    (* :973-977 *)
                    ClBad {| cl_have := cl_have s; cl_lens := cl_lens s;
                             cl_br := b2 |} MSG_BL_REPEAT
                  else
                    (* :978-979 *)
                    ClCont {| cl_have := cl_have s + cp;
                              cl_lens := zfill (Z.to_nat cp) (cl_lens s)
                                               (cl_have s) len;
                              cl_br   := b2 |}
              end
          end
    end.

(** The state after [k] fall-through trips, and the run to the exit.
    Every [ClCont] advances [cl_have] by at least 1 (by [cp >= 3] on the
    repeat arms), so [S (Z.to_nat tot)] trips always reach an exit. *)
Fixpoint cl_iter (k : nat) (t : ztbl) (nb tot : Z) (s : ClSt) {struct k}
  : option ClSt :=
  match k with
  | O => Some s
  | S k' => match cl_step t nb tot s with
            | ClCont s' => cl_iter k' t nb tot s'
            | _ => None
            end
  end.

Fixpoint cl_loop (n : nat) (t : ztbl) (nb tot : Z) (s : ClSt) {struct n}
  : option ClStep :=
  match n with
  | O => None
  | S k => match cl_step t nb tot s with
           | ClCont s' => cl_loop k t nb tot s'
           | r => Some r
           end
  end.

(** One [inflate_table] call, with the C's pointer bookkeeping:
    [*table] is [state->codes + k], the result advances it by [used] on
    success only, and [*bits] is left alone on an error return
    ([Inftrees]'s [o_bits] already encodes that). *)
Definition inf_table (st : IState) (ty : Z) (lens : zarr) (n root k : Z)
  : option (Z * Z * Z * ztbl) :=
  match it_model ty lens n root (fun i => t_codes (s_tab st) (k + i)) with
  | None => None
  | Some o => Some (o_ret o, o_bits o, k + o_used o,
                    codes_wb (t_codes (s_tab st)) k (o_tbl o))
  end.

(** [inflate.c:934-1022] [case CODELENS], falling through to LEN_. *)
Definition inf_CODELENS (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let bd := s_bld st in
  let tb := s_tab st in
  let tot := b_nlen bd + b_ndist bd in
  let put_cl (s : ClSt) : InfSt :=
    qset_br (qset_st q (set_lens (set_have st (cl_have s)) (cl_lens s)))
            (cl_br s) in
  match cl_loop (S (Z.to_nat tot)) (tbl_of st (t_lencode tb)) (t_lenbits tb)
                tot {| cl_have := b_have bd; cl_lens := b_lens bd;
                       cl_br := q_br q |} with
  | None             => InfFuel
  | Some ClFuel      => InfFuel
  | Some (ClCont _)  => InfFuel                     (* unreachable *)
  | Some (ClLeave s) => InfLeave (put_cl s)
  | Some (ClBad s m) => InfCont (qbad (put_cl s) m) (* :983 [if (mode == BAD) break] *)
  | Some (ClDone s) =>
      let q1 := put_cl s in
      let st1 := q_st q1 in
      if Z.eqb (cl_lens s 256) 0 then
        (* :986-991 *)
        InfCont (qbad q1 MSG_NO_EOB)
      else
        (* :996-1000: [state->next = state->codes; lencode = next; lenbits = 9] *)
        match inf_table st1 CT_LENS (cl_lens s) (b_nlen bd) 9 0 with
        | None => InfFuel
        | Some (rl, bl, nx, cd) =>
            let st2 := set_codes (set_next (set_lenbits
                          (set_lencode st1 (TRcodes 0)) bl) nx) cd in
            let q2 := qset_ret (qset_st q1 st2) rl in
            if negb (Z.eqb rl 0) then InfCont (qbad q2 MSG_LIT_LEN_SET)
            else
              (* :1010-1013 *)
              match inf_table st2 CT_DISTS
                      (fun i => cl_lens s (i + b_nlen bd)) (b_ndist bd) 6 nx with
              | None => InfFuel
              | Some (rd, bdst, nx2, cd2) =>
                  let st3 := set_codes (set_next (set_distbits
                                (set_distcode st2 (TRcodes nx)) bdst) nx2) cd2 in
                  let q3 := qset_ret (qset_st q2 st3) rd in
                  if negb (Z.eqb rd 0) then InfCont (qbad q3 MSG_DIST_SET)
                  else if Z.eqb (n_flush c) Z_TREES then
                    InfLeave (qmode q3 M_LEN_)
                  else inf_LEN_ (qmode q3 M_LEN_)
              end
        end
  end.

(** ** LENLENS's two [while]s — [inflate.c:911-916]

    Fuel 19: [ncode = BITS(4) + 4 <= 19] ([:894]), and both loops write at
    most 19 entries. *)
Inductive LlRes : Type :=
| LlOk    (have : Z) (lens : zarr) (b : BR)
| LlLeave (have : Z) (lens : zarr) (b : BR).

Fixpoint ll_go (f : nat) (ncode have : Z) (lens : zarr) (b : BR) {struct f}
  : LlRes :=
  match f with
  | O => LlOk have lens b
  | S k =>
      if Z.ltb have ncode then
        match inf_nb 3 b with
        | NBLeave b' => LlLeave have lens b'
        | NBOk b' =>
            ll_go k ncode (have + 1)
                  (zset lens (inf_order have) (br_bits_of 3 b'))
                  (br_dropbits 3 b')
        end
      else LlOk have lens b
  end.

Fixpoint ll_zero (f : nat) (have : Z) (lens : zarr) {struct f} : Z * zarr :=
  match f with
  | O => (have, lens)
  | S k => if Z.ltb have 19
           then ll_zero k (have + 1) (zset lens (inf_order have) 0)
           else (have, lens)
  end.

(** [inflate.c:910-933] [case LENLENS], falling through to CODELENS. *)
Definition inf_LENLENS (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let bd := s_bld st in
  match ll_go 19 (b_ncode bd) (b_have bd) (b_lens bd) (q_br q) with
  | LlLeave hv ls b =>
      InfLeave (qset_br (qset_st q (set_lens (set_have st hv) ls)) b)
  | LlOk hv ls b =>
      let '(hv1, ls1) := ll_zero 19 hv ls in
      let st1 := set_lens (set_have st hv1) ls1 in
      (* :917-920 *)
      match inf_table st1 CT_CODES ls1 19 7 0 with
      | None => InfFuel
      | Some (rc, bc, nx, cd) =>
          let st2 := set_codes (set_next (set_lenbits
                        (set_lencode st1 (TRcodes 0)) bc) nx) cd in
          let q1 := qset_ret (qset_br (qset_st q st2) b) rc in
          if negb (Z.eqb rc 0) then InfCont (qbad q1 MSG_CODE_LENGTHS)
          else inf_CODELENS c (qmode (qset_st q1 (set_have (q_st q1) 0))
                                     M_CODELENS)
      end
  end.

(** [inflate.c:888-909] [case TABLE], falling through to LENLENS.
    [PKZIP_BUG_WORKAROUND] is not defined, so the [:900-905] rejection is
    live. *)
Definition inf_TABLE (c : InfCtx) (q : InfSt) : InfStep :=
  match inf_nb 14 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let nlen  := br_bits_of 5 b + 257 in
      let b1    := br_dropbits 5 b in
      let ndist := br_bits_of 5 b1 + 1 in
      let b2    := br_dropbits 5 b1 in
      let ncode := br_bits_of 4 b2 + 4 in
      let b3    := br_dropbits 4 b2 in
      let st1   := set_ncode (set_ndist (set_nlen (q_st q) nlen) ndist) ncode in
      let q1    := qset_br (qset_st q st1) b3 in
      if Z.ltb 286 nlen || Z.ltb 30 ndist then InfCont (qbad q1 MSG_TOO_MANY)
      else inf_LENLENS c (qmode (qset_st q1 (set_have (q_st q1) 0)) M_LENLENS)
  end.

(** [inflate.c:875-887] [case COPY].  The copy is from the INPUT pointer,
    not through the bit accumulator: STORED's [BYTEBITS] + [INITBITS] left
    [bits = 0], so [next] is byte-aligned. *)
Definition inf_COPY (q : InfSt) : InfStep :=
  let st := q_st q in
  let b  := q_br q in
  let o  := q_ob q in
  let cp := u_length (s_cur st) in
  if Z.eqb cp 0 then InfCont (qmode q M_TYPE)
  else
    let c1 := if Z.ltb (br_have b) cp then br_have b else cp in
    let c2 := if Z.ltb (o_left o) c1 then o_left o else c1 in
    if Z.eqb c2 0 then InfLeave q
    else
      let o' := {| o_buf  := zcopy (Z.to_nat c2) (o_buf o) (o_put o)
                                   (br_in b) (br_next b);
                   o_put  := o_put o + c2;
                   o_left := o_left o - c2 |} in
      let b' := {| br_in := br_in b; br_have := br_have b - c2;
                   br_next := br_next b + c2;
                   br_hold := br_hold b; br_bits := br_bits b |} in
      InfCont (qset_ob (qset_br (qset_st q (set_length st (u32 (cp - c2)))) b') o').

(** [inflate.c:873-874] [case COPY_], falling through to COPY. *)
Definition inf_COPY_ (q : InfSt) : InfStep := inf_COPY (qmode q M_COPY).

(** [inflate.c:858-872] [case STORED], falling through to COPY_. *)
Definition inf_STORED (c : InfCtx) (q : InfSt) : InfStep :=
  match inf_nb 32 (br_bytebits (q_br q)) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      if negb (Z.eqb (Z.land (br_hold b) 65535)
                     (Z.lxor (Z.shiftr (br_hold b) 16) 65535)) then
        (* :861-865 *)
        InfCont (qbad (qset_br q b) MSG_STORED_LEN)
      else
        let st1 := set_length (q_st q) (Z.land (u32 (br_hold b)) 65535) in
        let q1  := qmode (qset_br (qset_st q st1) (br_initbits b)) M_COPY_ in
        if Z.eqb (n_flush c) Z_TREES then InfLeave q1 else inf_COPY_ q1
  end.

(** [inflate.c:245-290] [fixedtables]. *)
Definition fixedtables (s : IState) : IState :=
  set_distbits (set_distcode (set_lenbits (set_lencode s TRlenfix) 9) TRdistfix) 5.

(** [inflate.c:828-857] [case TYPEDO]. *)
Definition inf_TYPEDO (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  if negb (Z.eqb (h_last (s_hdr st)) 0) then
    (* :829-833 *)
    InfCont (qmode (qset_br q (br_bytebits (q_br q))) M_CHECK)
  else
    match inf_nb 3 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        let lastb := br_bits_of 1 b in
        let b1    := br_dropbits 1 b in
        let ty    := br_bits_of 2 b1 in
        let q1    := qset_br (qset_st q (set_last st lastb)) b1 in
        if Z.eqb ty 0 then
          (* :839-843 stored *)
          InfCont (qset_br (qmode q1 M_STORED) (br_dropbits 2 b1))
        else if Z.eqb ty 1 then
          (* :844-852 fixed *)
          let q2 := qmode (qset_st q1 (fixedtables (q_st q1))) M_LEN_ in
          if Z.eqb (n_flush c) Z_TREES
          then InfLeave (qset_br q2 (br_dropbits 2 b1))
          else InfCont (qset_br q2 (br_dropbits 2 b1))
        else if Z.eqb ty 2 then
          (* :853-856 dynamic *)
          InfCont (qset_br (qmode q1 M_TABLE) (br_dropbits 2 b1))
        else
          (* :857-859 *)
          InfCont (qset_br (qbad q1 MSG_BLOCK_TYPE) (br_dropbits 2 b1))
    end.

(** [inflate.c:825-827] [case TYPE], falling through to TYPEDO WITHOUT
    assigning [state->mode] — which [inf_leave]'s [data_type] can see. *)
Definition inf_TYPE (c : InfCtx) (q : InfSt) : InfStep :=
  if Z.eqb (n_flush c) Z_BLOCK || Z.eqb (n_flush c) Z_TREES then InfLeave q
  else inf_TYPEDO c q.

(** [inflate.c:815-823] [case DICT], falling through to TYPE. *)
Definition inf_DICT (c : InfCtx) (q : InfSt) : InfStep :=
  if Z.eqb (h_havedict (s_hdr (q_st q))) 0 then
    InfRet (q_restore q) Z_NEED_DICT
  else
    inf_TYPE c (qmode (qcheck q (adler32_z 0 true [])) M_TYPE).

(** [inflate.c:809-814] [case DICTID], falling through to DICT. *)
Definition inf_DICTID (c : InfCtx) (q : InfSt) : InfStep :=
  match inf_nb 32 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      inf_DICT c (qmode (qset_br (qcheck q (zswap32 (br_hold b)))
                                 (br_initbits b)) M_DICT)
  end.

(** The eight gzip header arms, [inflate.c:671-808] — transcribed
    2026-08-19 (zlib-rt Q3 gzip extension; until then they were [InfDead],
    the libpng-era dead-arm cut: entry is the gzip-magic branch of
    [inf_HEAD], gated on [state->wrap & 2], and libpng's
    [inflateInit2(strm, 0)] gave [wrap = 5]).  They are LIVE at
    [windowBits] 31/47 (wrap 6/7), z-repro's gzip and auto configs.

    [state->head] is [h_head], and it is 0 ([Z_NULL]) on every state this
    model can build: [inflateResetKeep] writes it and nothing else does —
    [inflateGetHeader] is not in the modeled surface, matching a driver
    that never calls it.  So the C's [if (state->head != Z_NULL)] writes
    into the header STRUCT are no-ops here; each is recorded at its line
    number, not transcribed.  [state->length] writes are NOT
    head-conditioned and are transcribed.

    In the C the fallthrough order is FLAGS -> TIME -> OS -> EXLEN ->
    EXTRA -> NAME -> COMMENT -> HCRC -> (TYPE via [break]); definitions
    below are in reverse so a fallthrough can CALL the next arm, per this
    file's convention. *)

(** [n] bytes of raw input at [br_next] — what the header-field CRC at
    [:737], [:759-760], [:778-779] is applied to.  The [ob_slice]
    counterpart for the INPUT array. *)
Definition br_slice (b : BR) (n : Z) : list Z :=
  map (fun k => br_in b (br_next b + Z.of_nat k)) (seq 0 (Z.to_nat n)).

(** [have -= copy; next += copy;] — raw byte consumption, [inf_COPY]'s
    idiom without the output write. *)
Definition br_consume (b : BR) (copy : Z) : BR :=
  {| br_in := br_in b; br_have := br_have b - copy;
     br_next := br_next b + copy;
     br_hold := br_hold b; br_bits := br_bits b |}.

(** [copy = 0; do { len = next[copy++]; } while (len && copy < have);]
    ([:753-758] NAME / [:772-777] COMMENT): consume up to and including
    the string terminator, or the whole input, whichever first.  Returns
    (copy, len).  Fuel [Z.to_nat have] suffices — every trip consumes one
    byte under the guard [copy < have] — so [None] is unreachable for
    [have >= 1]; the arms map it to [InfFuel], never a silent answer. *)
Fixpoint gz_strz (f : nat) (a : zarr) (i have copy : Z) {struct f}
  : option (Z * Z) :=
  match f with
  | O => None
  | S k =>
      let len := a i in
      let copy' := copy + 1 in
      if negb (Z.eqb len 0) && Z.ltb copy' have
      then gz_strz k a (i + 1) have copy'
      else Some (copy', len)
  end.

(** [inflate.c:786-808] [case HCRC], exiting to TYPE with a [break].
    [:799-803] head-struct writes skipped ([h_head] = 0); [:804] is the
    [strm->adler = state->check = crc32(0,Z_NULL,0)] pair write. *)
Definition inf_HCRC (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  if negb (Z.eqb (Z.land (h_flags h) 512) 0) then
    match inf_nb 16 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        if negb (Z.eqb (Z.land (h_wrap h) 4) 0)
           && negb (Z.eqb (br_hold b) (Z.land (h_check h) 65535)) then
          (* :791-794 *)
          InfCont (qbad (qset_br q b) MSG_HEADER_CRC)
        else
          InfCont (qmode (qcheck (qset_br q (br_initbits b))
                                 (crc32_z 0 true 0 [])) M_TYPE)
    end
  else
    InfCont (qmode (qcheck q (crc32_z 0 true 0 [])) M_TYPE).

(** [inflate.c:769-785] [case COMMENT], falling through to HCRC.
    [:774-776] head-struct writes skipped, so the do-while's
    [state->length++] (inside the head guard) never fires; unlike NAME
    there is NO trailing [state->length = 0] in this case. *)
Definition inf_COMMENT (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  if negb (Z.eqb (Z.land (h_flags h) 4096) 0) then
    let b := q_br q in
    if Z.eqb (br_have b) 0 then InfLeave q
    else
      match gz_strz (Z.to_nat (br_have b)) (br_in b) (br_next b) (br_have b) 0 with
      | None => InfFuel
      | Some (copy, len) =>
          let q1 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                       && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                    then qset_st q (set_check (q_st q)
                           (crc32_z (h_check h) false 0 (br_slice b copy)))
                    else q in
          let q2 := qset_br q1 (br_consume b copy) in
          if negb (Z.eqb len 0) then InfLeave q2
          else inf_HCRC (qmode q2 M_HCRC)
      end
  else
    (* :783-784 head write skipped *)
    inf_HCRC (qmode q M_HCRC).

(** [inflate.c:750-768] [case NAME], falling through to COMMENT.
    [:755-757] head-struct writes skipped; [:766] [state->length = 0] on
    both paths. *)
Definition inf_NAME (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  if negb (Z.eqb (Z.land (h_flags h) 2048) 0) then
    let b := q_br q in
    if Z.eqb (br_have b) 0 then InfLeave q
    else
      match gz_strz (Z.to_nat (br_have b)) (br_in b) (br_next b) (br_have b) 0 with
      | None => InfFuel
      | Some (copy, len) =>
          let q1 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                       && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                    then qset_st q (set_check (q_st q)
                           (crc32_z (h_check h) false 0 (br_slice b copy)))
                    else q in
          let q2 := qset_br q1 (br_consume b copy) in
          if negb (Z.eqb len 0) then InfLeave q2
          else inf_COMMENT
                 (qmode (qset_st q2 (set_length (q_st q2) 0)) M_COMMENT)
      end
  else
    (* :764-765 head write skipped *)
    inf_COMMENT (qmode (qset_st q (set_length (q_st q) 0)) M_COMMENT).

(** [inflate.c:725-749] [case EXTRA], falling through to NAME.
    [:731-738] the copy into [head->extra] is skipped ([h_head] = 0); the
    CRC at [:739-740] and the [length]/input bookkeeping at [:741-743]
    are not head-conditioned and are transcribed. *)
Definition inf_EXTRA (q : InfSt) : InfStep :=
  let st := q_st q in
  let h := s_hdr st in
  if negb (Z.eqb (Z.land (h_flags h) 1024) 0) then
    let b := q_br q in
    let copy0 := u_length (s_cur st) in
    let copy := if Z.ltb (br_have b) copy0 then br_have b else copy0 in
    let q2 :=
      if negb (Z.eqb copy 0) then
        let q1 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                     && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                  then qset_st q (set_check (q_st q)
                         (crc32_z (h_check h) false 0 (br_slice b copy)))
                  else q in
        qset_br (qset_st q1 (set_length (q_st q1) (copy0 - copy)))
                (br_consume b copy)
      else q in
    (* :745 [if (state->length) goto inf_leave;] *)
    if negb (Z.eqb (u_length (s_cur (q_st q2))) 0) then InfLeave q2
    else inf_NAME (qmode (qset_st q2 (set_length (q_st q2) 0)) M_NAME)
  else
    (* :747-748 head write skipped *)
    inf_NAME (qmode (qset_st q (set_length (q_st q) 0)) M_NAME).

(** [inflate.c:711-724] [case EXLEN], falling through to EXTRA.
    [:716-717] head write skipped. *)
Definition inf_EXLEN (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  if negb (Z.eqb (Z.land (h_flags h) 1024) 0) then
    match inf_nb 16 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        let st1 := set_length (q_st q) (br_hold b) in
        let st2 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                      && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                   then set_check st1 (crc32_z (h_check h) false 0
                          [Z.land (br_hold b) 255;
                           Z.land (Z.shiftr (br_hold b) 8) 255])
                   else st1 in
        inf_EXTRA (qmode (qset_br (qset_st q st2) (br_initbits b)) M_EXTRA)
    end
  else
    (* :722-723 head write skipped *)
    inf_EXTRA (qmode q M_EXTRA).

(** [inflate.c:700-710] [case OS], falling through to EXLEN.
    [:702-705] head writes skipped. *)
Definition inf_OS (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  match inf_nb 16 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let st1 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                    && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                 then set_check (q_st q) (crc32_z (h_check h) false 0
                        [Z.land (br_hold b) 255;
                         Z.land (Z.shiftr (br_hold b) 8) 255])
                 else q_st q in
      inf_EXLEN (qmode (qset_br (qset_st q st1) (br_initbits b)) M_EXLEN)
  end.

(** [inflate.c:691-699] [case TIME], falling through to OS.
    [:693-694] head write skipped; [:695-696] is [CRC4]. *)
Definition inf_TIME (q : InfSt) : InfStep :=
  let h := s_hdr (q_st q) in
  match inf_nb 32 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let st1 := if negb (Z.eqb (Z.land (h_flags h) 512) 0)
                    && negb (Z.eqb (Z.land (h_wrap h) 4) 0)
                 then set_check (q_st q) (crc32_z (h_check h) false 0
                        [Z.land (br_hold b) 255;
                         Z.land (Z.shiftr (br_hold b) 8) 255;
                         Z.land (Z.shiftr (br_hold b) 16) 255;
                         Z.land (Z.shiftr (br_hold b) 24) 255])
                 else q_st q in
      inf_OS (qmode (qset_br (qset_st q st1) (br_initbits b)) M_OS)
  end.

(** [inflate.c:671-690] [case FLAGS], falling through to TIME.
    [state->flags = (int)(hold)] takes the WHOLE accumulator, as the C
    does; the BAD exits keep [hold]/[bits] (no [INITBITS] before
    [break]), also as the C does.  [:683-684] head write skipped. *)
Definition inf_FLAGS (q : InfSt) : InfStep :=
  match inf_nb 16 (q_br q) with
  | NBLeave b => InfLeave (qset_br q b)
  | NBOk b =>
      let st1 := set_flags (q_st q) (br_hold b) in
      if negb (Z.eqb (Z.land (h_flags (s_hdr st1)) 255) Z_DEFLATED) then
        (* :674-677 *)
        InfCont (qbad (qset_br (qset_st q st1) b) MSG_UNKNOWN_METHOD)
      else if negb (Z.eqb (Z.land (h_flags (s_hdr st1)) 57344) 0) then
        (* :679-682 [0xe000] *)
        InfCont (qbad (qset_br (qset_st q st1) b) MSG_HEADER_FLAGS)
      else
        let st2 := if negb (Z.eqb (Z.land (h_flags (s_hdr st1)) 512) 0)
                      && negb (Z.eqb (Z.land (h_wrap (s_hdr st1)) 4) 0)
                   then set_check st1 (crc32_z (h_check (s_hdr st1)) false 0
                          [Z.land (br_hold b) 255;
                           Z.land (Z.shiftr (br_hold b) 8) 255])
                   else st1 in
        inf_TIME (qmode (qset_br (qset_st q st2) (br_initbits b)) M_TIME)
  end.

(** [inflate.c:588-649] [case HEAD]. *)
Definition inf_HEAD (c : InfCtx) (q : InfSt) : InfStep :=
  let st := q_st q in
  let h  := s_hdr st in
  if Z.eqb (h_wrap h) 0 then
    (* :589-592 raw stream *)
    inf_TYPEDO c (qmode q M_TYPEDO)
  else
    match inf_nb 16 (q_br q) with
    | NBLeave b => InfLeave (qset_br q b)
    | NBOk b =>
        if negb (Z.eqb (Z.land (h_wrap h) 2) 0) && Z.eqb (br_hold b) 35615 then
          (* :617-624 gzip magic 0x8b1f *)
          let st1 := if Z.eqb (w_wbits (s_win st)) 0 then set_wbits st 15 else st in
          let st2 := set_check st1 (crc32_z 0 true 0 []) in
          let ck  := crc32_z (h_check (s_hdr st2)) false 0
                             [Z.land (br_hold b) 255;
                              Z.land (Z.shiftr (br_hold b) 8) 255] in
          InfCont (qmode (qset_br (qset_st q (set_check st2 ck))
                                  (br_initbits b)) M_FLAGS)
        else if Z.eqb (Z.land (h_wrap h) 1) 0
                || negb (Z.eqb ((Z.shiftl (br_bits_of 8 b) 8
                                 + Z.shiftr (br_hold b) 8) mod 31) 0) then
          (* :626-631 *)
          InfCont (qbad (qset_br q b) MSG_HEADER_CHECK)
        else if negb (Z.eqb (br_bits_of 4 b) Z_DEFLATED) then
          (* :632-636 *)
          InfCont (qbad (qset_br q b) MSG_UNKNOWN_METHOD)
        else
          let b1  := br_dropbits 4 b in
          let len := br_bits_of 4 b1 + 8 in
          let st1 := if Z.eqb (w_wbits (s_win st)) 0 then set_wbits st len else st in
          if Z.ltb 15 len || Z.ltb (w_wbits (s_win st1)) len then
            (* :640-644 *)
            InfCont (qbad (qset_br (qset_st q st1) b1) MSG_WINDOW_SIZE)
          else
            let st2 := set_flags (set_dmax st1 (Z.shiftl 1 len)) 0 in
            let q1  := qcheck (qset_st q st2) (adler32_z 0 true []) in
            let m   := if Z.eqb (Z.land (br_hold b1) 512) 0 then M_TYPE else M_DICTID in
            let q2  := qset_br (qmode q1 m) (br_initbits b1) in
            InfCont q2
    end.

(** ** The [switch] — [inflate.c:586-1241] *)

Definition inf_step (c : InfCtx) (q : InfSt) : InfStep :=
  match q_mode q with
  | M_HEAD     => inf_HEAD c q
  | M_FLAGS    => inf_FLAGS q
  | M_TIME     => inf_TIME q
  | M_OS       => inf_OS q
  | M_EXLEN    => inf_EXLEN q
  | M_EXTRA    => inf_EXTRA q
  | M_NAME     => inf_NAME q
  | M_COMMENT  => inf_COMMENT q
  | M_HCRC     => inf_HCRC q
  | M_DICTID   => inf_DICTID c q
  | M_DICT     => inf_DICT c q
  | M_TYPE     => inf_TYPE c q
  | M_TYPEDO   => inf_TYPEDO c q
  | M_STORED   => inf_STORED c q
  | M_COPY_    => inf_COPY_ q
  | M_COPY     => inf_COPY q
  | M_TABLE    => inf_TABLE c q
  | M_LENLENS  => inf_LENLENS c q
  | M_CODELENS => inf_CODELENS c q
  | M_LEN_     => inf_LEN_ q
  | M_LEN      => inf_LEN q
  | M_LENEXT   => inf_LENEXT q
  | M_DIST     => inf_DIST q
  | M_DISTEXT  => inf_DISTEXT q
  | M_MATCH    => inf_MATCH q
  | M_LIT      => inf_LIT q
  | M_CHECK    => inf_CHECK q
  | M_LENGTH   => inf_LENGTH q
  | M_DONE     => inf_DONE q
  | M_BAD      => inf_BAD q
  | M_MEM      => inf_MEM q
  | M_SYNC     => inf_SYNC q
  end.

(** The state after [k] trips of the [for(;;)] that all ended in a
    [break] — the term a machine-level invariant on the dispatch head is
    indexed by. *)
Fixpoint inf_iter (k : nat) (c : InfCtx) (q : InfSt) {struct k} : option InfSt :=
  match k with
  | O => Some q
  | S k' => match inf_step c q with
            | InfCont q' => inf_iter k' c q'
            | _ => None
            end
  end.

Fixpoint inf_loop (n : nat) (c : InfCtx) (q : InfSt) {struct n} : option InfStep :=
  match n with
  | O => None
  | S k => match inf_step c q with
           | InfCont q' => inf_loop k c q'
           | r => Some r
           end
  end.

(** ** [inf_leave] — [inflate.c:1243-1273] *)

Definition inf_leave_tail (c : InfCtx) (q : InfSt) (wrote : Z) : InfSt * Z :=
  let st := q_st q in
  let h  := s_hdr st in
  let o  := q_ob q in
  let consumed := q_in q - br_have (q_br q) in           (* :1262 *)
  let q1 := qset_z q (zset_tin (q_z q) (z_tin (q_z q) + consumed)) in
  let q2 := qset_z q1 (zset_tout (q_z q1) (z_tout (q_z q1) + wrote)) in
  let q3 := qset_st q2 (set_total (q_st q2) (h_total h + wrote)) in
  let q4 := if negb (Z.eqb (Z.land (h_wrap h) 4) 0) && negb (Z.eqb wrote 0)
            then qcheck q3 (upd_check (h_flags h) (h_check h)
                                      (ob_slice o (o_put o - wrote) wrote))
            else q3 in
  let q5 := qset_out (qset_in q4 consumed) wrote in
  let m  := h_mode (s_hdr (q_st q5)) in
  (* :1268-1271 *)
  let dt := s_bits (q_st q5)
            + (if Z.eqb (h_last (s_hdr (q_st q5))) 0 then 0 else 64)
            + (match m with M_TYPE => 128 | _ => 0 end)
            + (match m with M_LEN_ | M_COPY_ => 256 | _ => 0 end) in
  let q6 := qset_z q5 (zset_dtype (q_z q5) dt) in
  (* :1272 *)
  let r := if ((Z.eqb consumed 0 && Z.eqb wrote 0) || Z.eqb (n_flush c) Z_FINISH)
              && Z.eqb (q_ret q6) Z_OK
           then Z_BUF_ERROR else q_ret q6 in
  (qset_ret q6 r, r).

Definition inf_leave (c : InfCtx) (q0 : InfSt) : InfSt * Z :=
  let q  := q_restore q0 in                              (* :1250 *)
  let st := q_st q in
  let o  := q_ob q in
  let wrote := q_out q - o_left o in
  let m  := h_mode (s_hdr st) in
  (* :1251-1256 *)
  if negb (Z.eqb (w_wsize (s_win st)) 0)
     || (negb (Z.eqb (q_out q) (o_left o))
         && Z.ltb (m_val m) (m_val M_BAD)
         && (Z.ltb (m_val m) (m_val M_CHECK)
             || negb (Z.eqb (n_flush c) Z_FINISH)))
  then
    match uw (n_walloc c) (n_wfresh c) st o wrote with
    | None => let q' := qset_ret (qmode q M_MEM) Z_MEM_ERROR in (q', Z_MEM_ERROR)
    | Some st' => inf_leave_tail c (qset_st q st') wrote
    end
  else inf_leave_tail c q wrote.

(** ** The whole call

    [inflateStateCheck] ([inflate.c:93-103]) fails on five conditions.
    Four of them cannot be expressed here (a NULL [strm], a NULL
    [zalloc]/[zfree], a [state] that does not point back at [strm], a
    [mode] outside the enum) and none is reachable; the fifth,
    [state == Z_NULL], IS reachable and is [g_state_null]. *)
Record InfArgs : Type := mkInfArgs {
  g_st        : IState;
  g_state_null : bool;  (** [strm->state == Z_NULL]: the one
                            [inflateStateCheck] condition ([:98]) that is
                            REACHABLE here — [pngpread.c:679] calls
                            [inflate] on the progressive reader's
                            [z_stream] without having claimed it, so a
                            corrupt PNG that never reaches
                            [png_inflate_claim] gets [Z_STREAM_ERROR]
                            straight out of [:580].  Observed on 40 of the
                            252 corpus files. *)
  g_z         : Strm;
  g_inbuf     : zarr;
  g_next_in   : Z;
  g_avail_in  : Z;
  g_in_null   : bool;
  g_outbuf    : zarr;
  g_next_out  : Z;
  g_avail_out : Z;
  g_out_null  : bool;
  g_flush     : Z;
  g_walloc    : bool;   (** does the window [ZALLOC] succeed? *)
  g_wfresh    : zarr
}.

Record InfRes : Type := mkInfRes { r_ret : Z; r_q : InfSt }.

Definition inf_st0 (a : InfArgs) : InfSt :=
  (* :584 [if (state->mode == TYPE) state->mode = TYPEDO;] *)
  let st0 := match h_mode (s_hdr (g_st a)) with
             | M_TYPE => set_mode (g_st a) M_TYPEDO
             | _ => g_st a
             end in
  {| q_st := st0; q_z := g_z a;
     q_br := {| br_in := g_inbuf a; br_have := g_avail_in a;
                br_next := g_next_in a;
                br_hold := s_hold st0; br_bits := s_bits st0 |};
     q_ob := {| o_buf := g_outbuf a; o_put := g_next_out a;
                o_left := g_avail_out a |};
     q_in := g_avail_in a; q_out := g_avail_out a; q_ret := Z_OK |}.

Definition inf_ctx (a : InfArgs) : InfCtx :=
  {| n_flush := g_flush a; n_walloc := g_walloc a; n_wfresh := g_wfresh a |}.

(** The lexicographic measure of c5-invariants.md §3.5, turned into a
    fuel: an arm that makes no input-or-output progress strictly raises
    the mode rank, and each of the four mode chains is acyclic, so 33
    trips per unit of [8 * avail_in + bits + avail_out] is an
    over-approximation of the trip count. *)
Definition inf_fuel (q : InfSt) : nat :=
  S (Z.to_nat (33 * (8 * br_have (q_br q) + br_bits (q_br q)
                     + o_left (q_ob q) + 1))).

(** [None] means the model declined on a fuel bound ([inf_wf] rules it
    out).  [InfDead] is retained in the [InfStep] type for interface
    stability but no arm produces it since the 2026-08-19 gzip
    transcription; its match arm below is unreachable. *)
Definition inflate_model (a : InfArgs) : option InfRes :=
  let q0 := inf_st0 a in
  if g_state_null a || g_out_null a
     || (g_in_null a && negb (Z.eqb (g_avail_in a) 0)) then
    Some {| r_ret := Z_STREAM_ERROR; r_q := q0 |}
  else
    let c := inf_ctx a in
    match inf_loop (inf_fuel q0) c q0 with
    | None              => None
    | Some InfFuel      => None
    | Some (InfDead _)  => None
    | Some (InfCont _)  => None                (* unreachable *)
    | Some (InfRet q r) => Some {| r_ret := r; r_q := q |}
    | Some (InfLeave q) =>
        let '(q', r) := inf_leave c q in Some {| r_ret := r; r_q := q' |}
    end.

(** ** Lifecycle — [inflate.c:105-207] and [:1245-1256]

    The allocations are call boundaries, so they are parameters: the
    [inflate_state] itself never fails to allocate in this model (its
    absence is not expressible), and the window's [ZALLOC] is
    [InfCtx]'s [n_walloc]. *)

(** [inflate.c:105-127] [inflateResetKeep]. *)
Definition inflateResetKeep (z : Strm) (s : IState) : Strm * IState :=
  let z1 := zset_msg (zset_tout (zset_tin z 0) 0) MSG_NONE in
  let z2 := if Z.eqb (h_wrap (s_hdr s)) 0 then z1
            else zset_adler z1 (Z.land (h_wrap (s_hdr s)) 1) in
  let s1 := set_back (set_sane
              (set_next (set_distcode (set_lencode
                (set_bits (set_hold
                  (set_head (set_dmax (set_flags (set_havedict
                    (set_last (set_mode (set_total s 0) M_HEAD) 0)
                  0) (-1)) 32768) 0)
                0) 0)
              (TRcodes 0)) (TRcodes 0)) 0)
            1) (-1) in
  (z2, s1).

(** [inflate.c:129-139] [inflateReset]. *)
Definition inflateReset (z : Strm) (s : IState) : Strm * IState :=
  inflateResetKeep z (set_wnext (set_whave (set_wsize s 0) 0) 0).

(** [inflate.c:141-171] [inflateReset2].  [None] is [Z_STREAM_ERROR].
    For libpng's [windowBits = 0] this gives [wrap = 5], [wbits = 0] —
    the configuration the whole file is written against. *)
Definition inflateReset2 (z : Strm) (s : IState) (windowBits : Z)
  : option (Strm * IState) :=
  let r := if Z.ltb windowBits 0 then
             (if Z.ltb windowBits (-15) then None else Some (0, - windowBits))
           else
             Some ((Z.shiftr windowBits 4) + 5,
                   if Z.ltb windowBits 48 then Z.land windowBits 15
                   else windowBits) in
  match r with
  | None => None
  | Some (wrap, wb) =>
      if negb (Z.eqb wb 0) && (Z.ltb wb 8 || Z.ltb 15 wb) then None
      else
        (* :162-165: free the window if the requested size changed *)
        let s1 := if w_alloc (s_win s) && negb (Z.eqb (w_wbits (s_win s)) wb)
                  then set_alloc s false else s in
        Some (inflateReset z (set_wbits (set_wrap s1 wrap) wb))
  end.

(** The freshly [ZALLOC]ed [inflate_state] before [inflateReset2] runs
    ([inflate.c:190-198]): [window = Z_NULL] and [mode = HEAD] are the
    only fields set, the rest is whatever the allocator left.  Those
    "rest" fields are parameters here rather than zeros, because
    [ZALLOC] does not zero ([zutil.c:298]) and every one of them is
    written by [inflateReset2]/[inflateResetKeep] before it is read. *)
Definition inflate_state0 (garbage : IState) : IState :=
  set_alloc (set_mode garbage M_HEAD) false.

(** [inflate.c:173-207] [inflateInit2_], minus the version/size checks
    ([:177-179]) and the [strm == Z_NULL] test, none of which this model
    can express.  [None] is [Z_STREAM_ERROR]. *)
Definition inflateInit2 (z : Strm) (garbage : IState) (windowBits : Z)
  : option (Strm * IState) :=
  inflateReset2 z (inflate_state0 garbage) windowBits.

(** [inflate.c:209-212] [inflateInit_]: [DEF_WBITS = 15]. *)
Definition inflateInit (z : Strm) (garbage : IState) : option (Strm * IState) :=
  inflateInit2 z garbage DEF_WBITS.

(** [inflate.c:1245-1256] [inflateEnd]: frees the window and the state.
    All that survives in this model is "the window is gone". *)
Definition inflateEnd (s : IState) : IState := set_alloc s false.

(** ** Well-formedness of a call

    The obligations that make the model's total functions equal to the C,
    plus the two that make the unmodelled arms unreachable.  Every call
    [png_inflate] makes satisfies them: [png_inflate_claim]
    ([pngrutil.c:406], [:415]) asks for [windowBits = 0], which
    [inflateReset2] turns into [wrap = 5], and nothing ever calls
    [inflateUndermine] or [inflateGetHeader]. *)
Definition inf_wf (a : InfArgs) : Prop :=
  (* The eight gzip arms are unreachable.  QUANTIFIER, because this
     conjunct has been read one scope too wide: it is true of RUNS from
     this entry state, NOT of arbitrary states.  [h_wrap] and [q_mode] are
     independent fields, so as a hypothesis on a single state this does
     NOT rule out [q_mode = M_FLAGS] — wp5-pf's
     [wrap_hypothesis_does_not_repair_Hstep] exhibits [wrap = 5] sitting in
     [M_FLAGS].  What blocks the arms step-by-step is the [gzip_off]
     conjunct of [INV] ([InvPreserve.v]), preserved because the single
     transition that can set a gzip mode is guarded at [Inflate.v:1504]. *)
  Z.land (h_wrap (s_hdr (g_st a))) 2 = 0
  (* [state->sane] is 1, so MATCH's compiled-out arm is unreachable *)
  /\ t_sane (s_tab (g_st a)) = 1
  (* [inflateGetHeader] is never called *)
  /\ h_head (s_hdr (g_st a)) = 0
  (* the buffers hold bytes *)
  /\ (forall i, 0 <= g_inbuf a i < 256)
  /\ (forall i, 0 <= g_outbuf a i < 256)
  /\ (forall i, 0 <= w_win (s_win (g_st a)) i < 256)
  /\ 0 <= g_avail_in a
  /\ 0 <= g_avail_out a
  (* [inflateReset2] leaves [wbits] either 0 (take it from the header) or
     a legal window exponent *)
  /\ (w_wbits (s_win (g_st a)) = 0 \/ 8 <= w_wbits (s_win (g_st a)) <= 15)
  (* MATCH's [do { } while (--copy)] needs a positive length; the arm is
     only entered from DISTEXT, whose length code base is at least 3 *)
  /\ (h_mode (s_hdr (g_st a)) = M_MATCH -> 1 <= u_length (s_cur (g_st a)))
  (* the CODELENS writes stay inside [lens[320]]; TABLE's check at
     [inflate.c:900] establishes this before CODELENS is ever entered *)
  /\ (h_mode (s_hdr (g_st a)) = M_CODELENS ->
        b_nlen (s_bld (g_st a)) <= 286 /\ b_ndist (s_bld (g_st a)) <= 30)
  (* ---------------------------------------------------------------
     Added 2026-08-16 by the LT (fuel-sufficiency) lane's findings, folded
     in by the interface arbiter.  These are the ENTRY-condition halves of
     six facts the termination measure needs; the LOOP-INVARIANT halves are
     published separately as carried facts for L6/L7 (see
     notes/wp4-roundtrip-manifest.md) because [inf_wf] is a precondition of
     a call and cannot state what must hold at every trip.

     MEASURED, not argued -- a precondition that is too strong is
     unprovable at establish time rather than merely useless.  All of the
     clauses below hold on 38,527 recorded [inflate] entry states from the
     delivered binary, spanning 9 distinct modes, with zero violations.

     [0 <= u_offset < 2^32] is the load-bearing one: without the upper
     bound, [u32 (offset - outd)] wraps to 0 in MATCH, [cw3] is 0, and the
     mode machine stays in MATCH forever on an unchanged state -- a real
     non-termination, not a proof inconvenience ([InflateThy.match_side]).
     --------------------------------------------------------------- *)
  /\ 0 <= u_offset (s_cur (g_st a)) < 4294967296
  /\ 0 <= u_length (s_cur (g_st a))
  /\ 0 <= w_wnext (s_win (g_st a))
  /\ 0 <= s_bits (g_st a).

(** ** Elementary facts

    Cheap, and each is used by the walk.  Anything substantial (that the
    table decode agrees with the canonical code, that the window holds the
    last [whave] bytes of the output history, termination) belongs to
    [Spec/PngModel/InflateThy.v] and to the machine-level lane. *)

(** The wrapper [inf_nb] and the frozen [br_needbits] agree wherever
    [br_needbits] commits to an answer — so nothing above silently forks
    from the lane's bit-reader interface; the wrapper only adds the state
    the C leaves behind on the [goto inf_leave] path, which [br_needbits]
    discards. *)
Lemma inf_nb_go_needbits :
  forall f n b b', inf_nb_go f n b = NBOk b' <-> br_needbits_go f n b = Some b'.
Proof.
  induction f as [|f IH]; intros n b b'; cbn [inf_nb_go br_needbits_go].
  - destruct (Z.ltb (br_bits b) n);
      split; intros H; try discriminate; congruence.
  - destruct (Z.ltb (br_bits b) n).
    + destruct (br_pullbyte b) as [b1|].
      * apply IH.
      * split; intros H; discriminate.
    + split; intros H; congruence.
Qed.

Lemma inf_nb_needbits :
  forall n b b', inf_nb n b = NBOk b' <-> br_needbits n b = Some b'.
Proof. intros n b b'; apply inf_nb_go_needbits. Qed.

(** The mode encoding is injective, so "the machine's mode register holds
    [m_val m]" pins [m]. *)
Lemma m_val_inj : forall m1 m2, m_val m1 = m_val m2 -> m1 = m2.
Proof. intros m1 m2; destruct m1, m2; cbn; congruence. Qed.

(** The unfolding lemmas the walk steps the outer loop with.  As in
    [InflateFast.v] these are [reflexivity] rather than [cbn], because
    the arms contain fuelled fixpoints whose literal unfolding is
    exponential. *)
Lemma inf_iter_O : forall c q, inf_iter 0 c q = Some q.
Proof. reflexivity. Qed.

Lemma inf_iter_S :
  forall k c q,
    inf_iter (S k) c q
    = match inf_step c q with InfCont q' => inf_iter k c q' | _ => None end.
Proof. reflexivity. Qed.

Lemma inf_loop_S :
  forall k c q,
    inf_loop (S k) c q
    = match inf_step c q with InfCont q' => inf_loop k c q' | r => Some r end.
Proof. reflexivity. Qed.

Lemma inf_iter_loop :
  forall k n c q q',
    inf_iter k c q = Some q' -> inf_loop (k + n) c q = inf_loop n c q'.
Proof.
  induction k as [|k IH]; intros n c q q' H.
  - rewrite inf_iter_O in H. inversion H; subst. reflexivity.
  - rewrite inf_iter_S in H.
    replace (S k + n)%nat with (S (k + n)) by reflexivity.
    rewrite inf_loop_S.
    destruct (inf_step c q); try discriminate H.
    now apply IH.
Qed.

(** Same three for CODELENS's inner loop. *)
Lemma cl_iter_O : forall t nb tot s, cl_iter 0 t nb tot s = Some s.
Proof. reflexivity. Qed.

Lemma cl_iter_S :
  forall k t nb tot s,
    cl_iter (S k) t nb tot s
    = match cl_step t nb tot s with ClCont s' => cl_iter k t nb tot s' | _ => None end.
Proof. reflexivity. Qed.

Lemma cl_loop_S :
  forall k t nb tot s,
    cl_loop (S k) t nb tot s
    = match cl_step t nb tot s with ClCont s' => cl_loop k t nb tot s' | r => Some r end.
Proof. reflexivity. Qed.

Lemma cl_iter_loop :
  forall k n t nb tot s s',
    cl_iter k t nb tot s = Some s' ->
    cl_loop (k + n) t nb tot s = cl_loop n t nb tot s'.
Proof.
  induction k as [|k IH]; intros n t nb tot s s' H.
  - rewrite cl_iter_O in H. inversion H; subst. reflexivity.
  - rewrite cl_iter_S in H.
    replace (S k + n)%nat with (S (k + n)) by reflexivity.
    rewrite cl_loop_S.
    destruct (cl_step t nb tot s); try discriminate H.
    now apply IH.
Qed.

(** ** Fuel monotonicity and the lexicographic measure

    FUEL MONOTONICITY.  A result obtained at ANY fuel is the result at
    every larger fuel, so a walk may prove termination at whatever bound
    is convenient and transfer it to [inf_fuel]. *)
Lemma inf_loop_fuel_mono :
  forall n n' c q r,
    (n <= n')%nat -> inf_loop n c q = Some r -> inf_loop n' c q = Some r.
Proof.
  induction n as [|n IH]; intros n' c q r Hle H.
  - cbn [inf_loop] in H. discriminate H.
  - destruct n' as [|n']; [lia|].
    rewrite inf_loop_S. rewrite inf_loop_S in H.
    destruct (inf_step c q) eqn:E.
    + apply IH; [lia | exact H].
    + exact H.
    + exact H.
    + exact H.
    + exact H.
Qed.

(** THE MEASURE named in the file header, turned into a definition.

    §3.5's lexicographic pair: the byte/bit budget
    [8 * avail_in + bits + avail_out] strictly decreases on every arm that
    consumes input or produces output, and the epsilon-transitions (the
    arms that only change [mode]) strictly RAISE the mode rank.  [m_val],
    the C enum's own numeric value ([m_val_range]: 16180..16211, so at
    most 32 of them in a row), does NOT have that property -- see
    [InflateThy.inf_rank_is_not_a_measure] and use
    [InflateThy.inf_mrank].  What survives here is the ARITHMETIC:
    [inf_fuel_dominates_rank] is about the width of the interval, so it
    holds for any permutation of it.  [inf_rank] flattens the pair into the single
    [nat] the fuel counts, at 33 trips per unit of budget — exactly the
    33 in [inf_fuel]. *)
Definition inf_budget (q : InfSt) : Z :=
  8 * br_have (q_br q) + br_bits (q_br q) + o_left (q_ob q).

Definition inf_rank (q : InfSt) : nat :=
  Z.to_nat (33 * inf_budget q + (16212 - m_val (q_mode q))).

Lemma m_val_range : forall m, 16180 <= m_val m <= 16211.
Proof. intros m; destruct m; cbn [m_val]; lia. Qed.

(** The fuel [inflate_model] actually picks DOMINATES that rank — which is
    the half of the termination argument that is arithmetic rather than
    per-arm, and the half that a reader is most likely to get wrong (the
    [+1] inside [inf_fuel] is what pays for the 32 mode steps). *)
Lemma inf_fuel_dominates_rank :
  forall q, 0 <= inf_budget q -> (inf_rank q < inf_fuel q)%nat.
Proof.
  intros q Hb. unfold inf_rank, inf_fuel.
  pose proof (m_val_range (q_mode q)) as Hm.
  assert (Hq : inf_budget q
               = 8 * br_have (q_br q) + br_bits (q_br q) + o_left (q_ob q))
    by reflexivity.
  lia.
Qed.

(** NOT PROVED HERE, and deliberately not claimed: the per-arm decrease
    [inf_step c q = InfCont q' -> (inf_rank q' < inf_rank q)%nat].  It is
    one obligation per mode arm (twenty-odd of them), each needing that
    arm's own effect on [br_have]/[br_bits]/[o_left]/[mode], and it is
    round-trip work rather than hygiene.  [inf_rank] and
    [inf_fuel_dominates_rank] fix the shape it has to be proved against,
    so the lanes cannot each pick a different one. *)

(** MATCH's byte-at-a-time copy advances the write cursor by exactly [n]
    and touches nothing below it. *)
Lemma ob_copyn_put :
  forall n win o r, o_put (ob_copyn n win o r) = o_put o + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros win o r; cbn [ob_copyn]; [cbn; lia|].
  rewrite IH. cbn [ob_write o_put]. lia.
Qed.

Lemma ob_copyn_left :
  forall n win o r, o_left (ob_copyn n win o r) = o_left o - Z.of_nat n.
Proof.
  induction n as [|n IH]; intros win o r; cbn [ob_copyn]; [cbn; lia|].
  rewrite IH. cbn [ob_write o_left]. lia.
Qed.

Lemma ob_copyn_below :
  forall n win o r j,
    j < o_put o -> o_buf (ob_copyn n win o r) j = o_buf o j.
Proof.
  induction n as [|n IH]; intros win o r j Hj; cbn [ob_copyn]; [reflexivity|].
  rewrite IH by (cbn [ob_write o_put]; lia).
  cbn [ob_write o_buf]. apply zset_other. lia.
Qed.

(** [zcopy] writes exactly [n] entries and leaves everything else alone —
    the two facts a [WIN_rep] needs across [updatewindow]'s [zmemcpy]s. *)
Lemma zcopy_miss :
  forall n dst di src si j,
    (forall m, (m < n)%nat -> j <> di + Z.of_nat m) ->
    zcopy n dst di src si j = dst j.
Proof.
  induction n as [|n IH]; intros dst di src si j Hm; cbn [zcopy]; [reflexivity|].
  rewrite IH.
  - apply zset_other. intros ->. apply (Hm 0%nat); lia.
  - intros m Hlt. specialize (Hm (S m) ltac:(lia)). lia.
Qed.

Lemma zcopy_hit :
  forall n dst di src si m,
    (m < n)%nat ->
    zcopy n dst di src si (di + Z.of_nat m) = src (si + Z.of_nat m).
Proof.
  induction n as [|n IH]; intros dst di src si m Hm; [lia|]. cbn [zcopy].
  destruct m as [|m'].
  - replace (di + Z.of_nat 0) with di by lia.
    rewrite zcopy_miss by (intros k Hk; lia).
    replace (si + Z.of_nat 0) with si by lia.
    apply zset_same.
  - replace (di + Z.of_nat (S m')) with (di + 1 + Z.of_nat m') by lia.
    rewrite IH by lia. f_equal; lia.
Qed.

(** [zfill] likewise — CODELENS's [while (copy--) lens[have++] = len]. *)
Lemma zfill_miss :
  forall n a i v j,
    (forall m, (m < n)%nat -> j <> i + Z.of_nat m) ->
    zfill n a i v j = a j.
Proof.
  induction n as [|n IH]; intros a i v j Hm; cbn [zfill]; [reflexivity|].
  rewrite IH.
  - apply zset_other. intros ->. apply (Hm 0%nat); lia.
  - intros m Hlt. specialize (Hm (S m) ltac:(lia)). lia.
Qed.

Lemma zfill_hit :
  forall n a i v m, (m < n)%nat -> zfill n a i v (i + Z.of_nat m) = v.
Proof.
  induction n as [|n IH]; intros a i v m Hm; [lia|]. cbn [zfill].
  destruct m as [|m'].
  - replace (i + Z.of_nat 0) with i by lia.
    rewrite zfill_miss by (intros k Hk; lia). apply zset_same.
  - replace (i + Z.of_nat (S m')) with (i + 1 + Z.of_nat m') by lia.
    apply IH; lia.
Qed.

(** [zcopy] / [zfill] as RANGE facts.  The [_miss] lemmas above are
    pointwise with a per-index side condition; every window invariant
    wants the window, and [Base]'s [arr_eq_on] is the shape the rest of
    the tree composes with. *)
Lemma zcopy_arr_eq_on :
  forall n dst di src si lo hi,
    (forall m, (m < n)%nat -> ~ (lo <= di + Z.of_nat m < hi)) ->
    arr_eq_on (zcopy n dst di src si) dst lo hi.
Proof.
  intros n dst di src si lo hi Hmiss j Hj.
  apply zcopy_miss. intros m Hm Heq. apply (Hmiss m Hm). now rewrite <- Heq.
Qed.

Lemma zcopy_arr_eq_on_below :
  forall n dst di src si lo,
    arr_eq_on (zcopy n dst di src si) dst lo di.
Proof.
  intros n dst di src si lo. apply zcopy_arr_eq_on.
  intros m Hm [H1 H2]. lia.
Qed.

Lemma zfill_arr_eq_on :
  forall n a i v lo hi,
    (forall m, (m < n)%nat -> ~ (lo <= i + Z.of_nat m < hi)) ->
    arr_eq_on (zfill n a i v) a lo hi.
Proof.
  intros n a i v lo hi Hmiss j Hj.
  apply zfill_miss. intros m Hm Heq. apply (Hmiss m Hm). now rewrite <- Heq.
Qed.

Lemma zfill_arr_eq_on_below :
  forall n a i v lo, arr_eq_on (zfill n a i v) a lo i.
Proof.
  intros n a i v lo. apply zfill_arr_eq_on. intros m Hm [H1 H2]. lia.
Qed.

(** The configuration libpng asks for, pinned.  [png_inflate_claim]
    ([pngrutil.c:415]) calls [inflateInit2(&zstream, 0)] and, on every
    later chunk, [inflateReset2(&zstream, 0)] ([:406]); [inflateReset2]
    turns [windowBits = 0] into [wrap = (0 >> 4) + 5 = 5] and
    [wbits = 0 & 15 = 0] ([inflate.c:155-159]).  Those two numbers are
    what make the eight gzip arms unreachable ([wrap & 2 = 0]) and the
    window size header-driven rather than a constant 32768.  Independent
    of whatever the allocator left in the fresh state.

    Corroborated on the delivered binary: all 6580 recorded [inflate]
    calls with a non-NULL state have [wrap = 5] and [sane = 1], and
    [wsize] ranges over 256..32768 rather than being constant. *)
Lemma png_inflate_claim_config :
  forall g z,
    match inflateInit2 z g 0 with
    | Some (_, s) =>
        h_wrap (s_hdr s) = 5
        /\ Z.land (h_wrap (s_hdr s)) 2 = 0     (* no gzip: FLAGS.. are dead *)
        /\ Z.land (h_wrap (s_hdr s)) 1 = 1     (* the zlib header IS checked *)
        /\ Z.land (h_wrap (s_hdr s)) 4 = 4     (* the ADLER trailer IS checked *)
        /\ w_wbits (s_win s) = 0               (* window size from the header *)
        /\ h_mode (s_hdr s) = M_HEAD
        /\ h_flags (s_hdr s) = -1
        /\ h_dmax (s_hdr s) = 32768
        /\ h_head (s_hdr s) = 0                (* inflateGetHeader arms dead *)
        /\ t_sane (s_tab s) = 1                (* MATCH's sane arm dead *)
        /\ u_back (s_cur s) = -1
        /\ w_wsize (s_win s) = 0
        /\ w_alloc (s_win s) = false
    | None => False
    end.
Proof. intros g z. cbn. repeat split. Qed.

(** ** Cross-validation of [inffixed.h] against [Inftrees]

    [makefixed] ([inflate.c:311-347]) is what generated [inffixed.h], and
    it does NOT print [inflate_table]'s output verbatim: line 328 is

<<
        printf("{%u,%u,%d}", (low & 127) == 99 ? 64 : state.lencode[low].op,
               state.lencode[low].bits, state.lencode[low].val);
>>

    so the four slots with [(low & 127) == 99] get [op = 64] instead of
    what [inflate_table] computed.  Those are the root-table entries for
    the unused length symbols 286 and 287, whose [op] comes from
    [inftrees.c:60]'s deliberate garbage [lext[29] = 203] and
    [lext[30] = 77].  A [-DBUILDFIXED] build would therefore hold
    DIFFERENT BYTES in those four entries than the shipped
    [inffixed.h]-using build does — which is exactly why the
    transcription above carries [inffixed.h]'s literals and not a call to
    [it_model].

    These three [vm_compute] facts pin all of it, and tie this file's
    tables to the already binary-validated [Spec/PngModel/Inftrees.v]. *)

Definition fixed_lens_l : zarr :=
  fun i => if Z.ltb i 144 then 8 else if Z.ltb i 256 then 9
           else if Z.ltb i 280 then 7 else 8.
Definition fixed_lens_d : zarr := fun _ => 5.

(** [inflate.c:264-271] then [:277-279]: the two [inflate_table] calls a
    [BUILDFIXED] build would make.  Both succeed, with the root sizes and
    entry counts [fixedtables] hard-codes. *)
Lemma fixedtables_shape :
  match it_model CT_LENS fixed_lens_l 288 9 tnone,
        it_model CT_DISTS fixed_lens_d 32 5 tnone with
  | Some ol, Some od =>
      (o_ret ol, o_bits ol, o_used ol, o_ret od, o_bits od, o_used od)
      = (0, 9, 512, 0, 5, 32)
  | _, _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** [distfix] IS [inflate_table]'s output — no symbol of the fixed
    distance code is unused, so [makefixed]'s patch never fires there. *)
Lemma distfix_is_inflate_table :
  match it_model CT_DISTS fixed_lens_d 32 5 tnone with
  | Some o => forallb (fun k => code_eqb (o_tbl o (Z.of_nat k))
                                         (distfix (Z.of_nat k)))
                      (seq 0 32) = true
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** [lenfix] agrees with [inflate_table] EXCEPT at exactly the four
    [(low & 127) == 99] slots, where [inffixed.h] has [op = 64] and
    [inflate_table] would have [lext[29] = 203] / [lext[30] = 77]. *)
Lemma lenfix_differs_only_at_makefixed_patch :
  match it_model CT_LENS fixed_lens_l 288 9 tnone with
  | Some o =>
      filter (fun k => negb (code_eqb (o_tbl o (Z.of_nat k))
                                      (lenfix (Z.of_nat k))))
             (seq 0 512)
      = [99; 227; 355; 483]%nat
      /\ map (fun k => (c_op (o_tbl o (Z.of_nat k)), c_op (lenfix (Z.of_nat k)),
                        c_bits (lenfix (Z.of_nat k)), c_val (lenfix (Z.of_nat k))))
             [99; 227; 355; 483]%nat
         = [(203, 64, 8, 0); (77, 64, 8, 0); (203, 64, 8, 0); (77, 64, 8, 0)]
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** ...and the patch is not observable through the decoder: 203, 77 and
    64 all have bit 6 set and bits 4,5 clear and the high nibble nonzero,
    so LEN ([inflate.c:1041], [:1059], [:1065]) and [inflate_fast]
    ([inffast.c:118], [:251], [:263]) take the same
    "invalid literal/length code" branch on all three.  The bytes differ,
    the behaviour does not — which is why the machine-level walk must use
    [lenfix] but the round-trip theorem need not care. *)
Lemma makefixed_patch_decodes_the_same :
  forallb (fun op => (negb (Z.eqb (Z.land op 240) 0))     (* not a sub-table *)
                     && Z.eqb (Z.land op 16) 0            (* not a length base *)
                     && Z.eqb (Z.land op 32) 0            (* not end-of-block *)
                     && negb (Z.eqb (Z.land op 64) 0))    (* invalid code *)
          [203; 77; 64] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** gzip-arm controls (2026-08-19 Q3 extension)

    Differentially validated against zlib-1.3.1 ITSELF (the shipped
    problem source compiled host-side; harness
    [a working folder]): every vector below was run
    through the real [inflate()] with the same windowBits/flush/cap, and
    (rc, total_in, output) agree exactly — including the four rejection
    paths and the fully-loaded header that walks all eight arms.  The
    plumbing mirrors [Codec.z_fresh]/[state_fresh] (not imported: Codec
    Requires THIS file). *)

Definition gzctl_state0 : IState :=
  {| s_hdr := {| h_mode := M_HEAD; h_last := 0; h_wrap := 0; h_havedict := 0;
                 h_flags := 0; h_dmax := 0; h_check := 0; h_total := 0;
                 h_head := 0 |};
     s_win := {| w_wbits := 0; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := 0; u_offset := 0; u_extra := 0; u_back := 0;
                 u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 0; t_distbits := 0; t_next := 0;
                 t_codes := tnone; t_sane := 0 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zlist []; b_work := zlist [] |};
     s_hold := 0; s_bits := 0 |}.

Definition gzctl_z0 : Strm :=
  {| z_tin := 0; z_tout := 0; z_adler := 0; z_dtype := 0; z_msg := 0 |}.

(** One [inflate] call on a fresh stream: (ret, consumed, out). *)
Definition gzctl (flush wb availin cap : Z) (enc : list Z)
  : option (Z * Z * list Z) :=
  match inflateInit2 gzctl_z0 gzctl_state0 wb with
  | None => None
  | Some (z, s) =>
      match inflate_model {| g_st := s; g_state_null := false; g_z := z;
                             g_inbuf := zlist enc; g_next_in := 0;
                             g_avail_in := availin; g_in_null := false;
                             g_outbuf := zzero; g_next_out := 0;
                             g_avail_out := cap; g_out_null := false;
                             g_flush := flush; g_walloc := true;
                             g_wfresh := zzero |} with
      | None => None
      | Some r => Some (r_ret r, availin - br_have (q_br (r_q r)),
                        ob_slice (q_ob (r_q r)) 0 (o_put (q_ob (r_q r))))
      end
  end.

(** The (9,31) level-9 stream for input "H" — [Deflate.v]'s
    [gzip_stream_level9_H], byte-validated there. *)
Definition gzctl_basic : list Z :=
  [31;139;8;0;0;0;0;0;2;3; 243;0;0; 47;38;5;170; 1;0;0;0].

(** deflateSetHeader-generated (real zlib): FLG = 0x1f
    (FTEXT|FHCRC|FEXTRA|FNAME|FCOMMENT), MTIME 0x01020304, XLEN 3 extra
    aa bb cc, name "nm", comment "cm", header CRC16 0x2eb1 — walks
    FLAGS/TIME/OS/EXLEN/EXTRA/NAME/COMMENT/HCRC in one call. *)
Definition gzctl_loaded : list Z :=
  [31;139;8;31; 4;3;2;1; 2;3; 3;0; 170;187;204; 110;109;0; 99;109;0; 177;46;
   243;0;0; 47;38;5;170; 1;0;0;0].

(** zlib-1.3.1: rc=1 totin=21 out="H" — and via wb 47 auto-detect. *)
Example gz_rt_basic : gzctl 4 31 21 16 gzctl_basic = Some (1, 21, [72]).
Proof. vm_compute. reflexivity. Qed.
Example gz_rt_auto : gzctl 4 47 21 16 gzctl_basic = Some (1, 21, [72]).
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: rc=0 totin=2 — magic consumed, FLAGS starves, clean
    inf_leave. *)
Example gz_partial_magic : gzctl 0 47 2 16 [31;139] = Some (0, 2, []).
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: rc=-3 "unknown compression method" / "unknown header
    flags set" — FLAGS' two BAD exits. *)
Example gz_bad_cm : gzctl 0 47 4 16 [31;139;7;0] = Some (-3, 4, []).
Proof. vm_compute. reflexivity. Qed.
Example gz_bad_flags : gzctl 0 47 4 16 [31;139;8;224] = Some (-3, 4, []).
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: rc=-3 "incorrect data check" (CRC32 corrupted, totin 17)
    / "incorrect length check" (ISIZE corrupted, totin 21) — the gzip
    sides of CHECK and LENGTH. *)
Example gz_bad_crc32 :
  gzctl 4 31 21 16 [31;139;8;0;0;0;0;0;2;3; 243;0;0; 47;38;5;171; 1;0;0;0]
  = Some (-3, 17, [72]).
Proof. vm_compute. reflexivity. Qed.
Example gz_bad_isize :
  gzctl 4 31 21 16 [31;139;8;0;0;0;0;0;2;3; 243;0;0; 47;38;5;170; 2;0;0;0]
  = Some (-3, 21, [72]).
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: rc=1 totin=34 out="H" through ALL EIGHT arms; corrupting
    the header CRC16 gives rc=-3 "header crc mismatch" at totin=23. *)
Example gz_loaded_header_all_arms :
  gzctl 4 31 34 16 gzctl_loaded = Some (1, 34, [72]).
Proof. vm_compute. reflexivity. Qed.
Example gz_bad_hcrc :
  gzctl 4 31 34 16 (firstn 21 gzctl_loaded ++ [178;46] ++ skipn 23 gzctl_loaded)
  = Some (-3, 23, []).
Proof. vm_compute. reflexivity. Qed.

(** Cross-call re-entry through the header arms: the loaded stream split
    mid-MTIME (after byte 5).  Call 1 leaves inside TIME with the partial
    accumulator ([inf_nb] keeps it); call 2 finishes.  zlib-1.3.1
    byte-at-a-time chunking agrees (final rc=1, out="H"). *)
Example gz_split_reentry :
  match inflateInit2 gzctl_z0 gzctl_state0 31 with
  | None => False
  | Some (z, s) =>
      match inflate_model {| g_st := s; g_state_null := false; g_z := z;
                             g_inbuf := zlist (firstn 5 gzctl_loaded);
                             g_next_in := 0; g_avail_in := 5;
                             g_in_null := false;
                             g_outbuf := zzero; g_next_out := 0;
                             g_avail_out := 16; g_out_null := false;
                             g_flush := 0; g_walloc := true;
                             g_wfresh := zzero |} with
      | None => False
      | Some r1 =>
          match inflate_model {| g_st := q_st (r_q r1); g_state_null := false;
                                 g_z := q_z (r_q r1);
                                 g_inbuf := zlist (skipn 5 gzctl_loaded);
                                 g_next_in := 0; g_avail_in := 29;
                                 g_in_null := false;
                                 g_outbuf := zzero; g_next_out := 0;
                                 g_avail_out := 16; g_out_null := false;
                                 g_flush := 4; g_walloc := true;
                                 g_wfresh := zzero |} with
          | None => False
          | Some r2 =>
              (r_ret r1, r_ret r2,
               ob_slice (q_ob (r_q r2)) 0 (o_put (q_ob (r_q r2))))
              = (0, 1, [72])
          end
      end
  end.
Proof. vm_compute. reflexivity. Qed.
