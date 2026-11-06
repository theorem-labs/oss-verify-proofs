(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c, Img0.rsegs): the per-build part of the kit for the
    satisfiability lemmas of contract family F1 (the build-independent part: Prog/SegSatKit.v; the lemmas:
    Prog/sat/F1Sat.v). proves no function (kind: statement text; closed satisfiability lemmas of contract premises).

    The image's segments end below SegSatKit.IMG_END (the last, rw- at 0x22000, ends at 0x54000), so every region
    of the witness memories lies outside the image: mem_inv, the stack's seg_rom = None.

    The frames between LLVMFuzzerTestOneInput and each function (plain binary), from main's entry sp S_TOP:
    - main: `addi sp,sp,-0xd0` (208); its stack area at sp + 0x40 holds label[40], then r (0x5a; the role out cell),
      then probe[18], then v.
    - the reader's accessors (reac_segconf_role, _ignored, _role_file, _ignore_file, _model): 16 bytes each;
      check_absent: 32.
    - reac_segconf_parse (the last file): 32 (`addi sp,sp,-0x20`); reac_segconf_parse_file: 976
      (`addi sp,sp,-0x3d0`); its low[24] at sp + 0x140 is reac_box_catalogue_by_token's argument. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec SegSatKit.
Import ListNotations.
Open Scope Z_scope.

Lemma rsegs_below : segs_below rsegs IMG_END = true.
Proof. vm_compute. reflexivity. Qed.

Definition MAIN_FRAME : Z := 208.
Definition SP_MAIN : Z := S_TOP - MAIN_FRAME.
Definition OUT : Z := SP_MAIN + 0x40.
Definition ACC_FRAME : Z := 16.
Definition ABSENT_FRAME : Z := 32.
Definition PARSE_FRAME : Z := 32.
Definition PF_FRAME : Z := 976.
Definition SP_PF : Z := SP_MAIN - PARSE_FRAME - PF_FRAME.
Definition TOKA : Z := SP_PF + 0x140.
(** reac_segconf_parse_file called by main itself, for a drop-in file (fuzz_segconf.c:613, 0x13a18). *)
Definition SP_PF2 : Z := SP_MAIN - PF_FRAME.
Definition TOKA2 : Z := SP_PF2 + 0x140.

(** The witness memories, one per moment of the run (the first region holding an address gives its byte):
    - RS_INIT at reac_segconf_init: c = malloc(16616) (contents not fixed: zeros), m = calloc's zeros;
    - RSQ r at the per-segment checks: main's cell r at OUT, c holding RC0, m holding MC0;
    - RSP at check_absent and the queries it makes: the probe "<name>x" in probe[18] at OUT;
    - RST at reac_box_catalogue_by_token: low[24] holding the folded model value and its NUL (RST2: the same
      under a drop-in parse_file);
    - RSD at check_declared: the tab and mt blocks as well. *)
Definition RS_INIT : list region := [(C0, zrep 16616); (M0, zrep 9236); R_STACK].
Definition RSQ (r : Z) : list region := [(OUT, le4z r); (C0, rconf_img RC0); (M0, mconf_img MC0); R_STACK].
Definition RSP : list region := [(OUT, padz PROBE0 18); (C0, rconf_img RC0); (M0, mconf_img MC0); R_STACK].
Definition RST : list region := [(TOKA, padz LOW0 24); R_STACK].
Definition RST2 : list region := [(TOKA2, padz LOW0 24); R_STACK].
Definition RSD : list region :=
  [(C0, rconf_img RC0); (M0, mconf_img MC0); (TAB0, tab_img (snd GOT0) CAP0); (MT0, mt_img (snd WANT0) CAP0);
   R_STACK].
