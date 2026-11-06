From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_parse_file(c, text, label) (reac_segconf.c:120-296; at 0x15248 in the UBSan image 1696d6c34ffd; frame 0x420, saves ra and
    s0-s11): snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf"), c->gen++,
    then (text <> NULL: the premise; the NULL path returns c->n before the loop and no call site takes it) the line
    loop over the text with cur = NULL and cur_name = "", one line per pass (strchr(p, '\n'), the >= 512 refusal, the
    copy into buf[512], strip_comment, trim, then the header or the key line), and returns c->n (`lw` c + 0x2c80).
    The walk is split into the 9 pieces and the line-loop invariant of reac_segconf_parse_file_pieces_c.v (family
    F3); this file states the whole function.

    Post in the spine's terms: a0 = snd (SegModel.r_parse_file rc s lab) and c holds fst (...). It writes its frame
    and its callees' frames below sp (refuse is the deepest: REFUSE_STACK) and exactly seg_spec.RC_PARSE_W c: seg[32],
    n, refusal[8], n_refusals, refused, overflow, reading, gen. The text is never written (every edit is in buf).

    Callee contracts its walk takes as premises (through the pieces): snprintf, refuse, trim, strchr, strlen, strspn,
    memcpy, memset, strncasecmp, strcasecmp, bcmp, strcmp, reac_box_catalogue_by_token, reac_box_catalogue (this
    directory).

    Call sites: LLVMFuzzerTestOneInput 0x13b4c (c, text = fuzz_str's block, l = NULL, main's label buffer or longl,
    for every file but the last) and reac_segconf_parse 0x15e9c (c, text, "reac-pw.conf"). At each: c the 16-aligned
    reader block holding the state after the earlier files; text a C string of at most 65535 bytes (fuzz_take of a u16
    length) in its own malloc block (slack: the frame's block_slack_present); the label a C string (at most 120 bytes)
    in main's frame, in .bss (longl, 120 'L' and the NUL GI keeps at byte 120) or .rodata. *)
Definition REAC_SEGCONF_PARSE_FILE : Z := 0x15248.
Definition PARSE_FILE_FRAME : Z := 0x420.
Definition PARSE_FILE_STACK : Z := PARSE_FILE_FRAME + REFUSE_STACK.

(** What every caller of the reader's parse supplies (all but the label): the reader block holding rc (its counters
    far from 2^32: at most 65536 lines a call), the text, printf's machine, the box-model table, the stack. *)
Definition reader_pre (depth : Z) (m : word -> option byte) (fc : bv 32) (sp lo c t : Z) (rc : rconf) (s : list Z)
    : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ rconf_at rsegs m c rc /\ apart c SEG_C_SIZE lo sp /\ blk_noimg rsegs c SEG_C_SIZE /\
  rc_gen rc + 1 < 2 ^ 32 /\ rc_refused rc + 2 ^ 17 < 2 ^ 32 /\ rc_overflow rc + 2 ^ 17 < 2 ^ 32 /\
  t <> 0 /\ cstr_at rsegs m t s /\ (length s <= 65535)%nat /\
  apart t (Z.of_nat (length s) + 8) lo sp /\ apart t (cstr_span t s) c (c + SEG_C_SIZE) /\
  printf_env m fc lo sp /\ cat_img rsegs m (sa_catalogue SA) /\ stack_ok rsegs m lo sp depth /\ mem_inv rsegs m.

Definition reac_segconf_parse_file_pre (m : word -> option byte) (fc : bv 32) (sp lo c t lp : Z) (rc : rconf)
    (s : list Z) (lab : option (list Z)) : Prop :=
  reader_pre PARSE_FILE_STACK m fc sp lo c t rc s /\
  ocstr_at rsegs m lp lab /\
  (match lab with
   | Some l => (length l <= 65535)%nat /\ apart lp (Z.of_nat (length l) + 8) lo sp /\
               apart lp (Z.of_nat (length l) + 8) (c + RC_READING) (c + RC_READING + 96)
   | None => True
   end).

Definition reac_segconf_parse_file_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (s : list Z) (lab : option (list Z)),
    reac_segconf_parse_file_pre m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) rc s lab ->
    evt rsegs
      (ret_post_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         (snd (r_parse_file rc s lab))
         m
         ((bv_unsigned sp - PARSE_FILE_STACK, bv_unsigned sp) :: RC_PARSE_W (bv_unsigned a0))
         lo
         (fun m' => rconf_at rsegs m' (bv_unsigned a0) (fst (r_parse_file rc s lab))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_PARSE_FILE) fc None m (seg_rom rsegs)).
