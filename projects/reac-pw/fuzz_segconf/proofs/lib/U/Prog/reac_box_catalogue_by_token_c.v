From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import fuzz_catalogue_row_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_box_catalogue_by_token(token) (catalogue.c:47-50; 52 bytes, 13 instructions at 0x167a0 in the UBSan image
    1696d6c34ffd): NULL returns 0 at once (`beqz a0`, before any frame; no call site passes NULL: the premise excludes
    it); else a 16-byte frame (saves ra, s0 = token), n = strlen(token) (`jal strlen`, 0x1f5cc), the frame popped
    (ra and s0 restored), then the tail call `j fuzz_catalogue_row` (0x166f4) with a0 = token, a1 = n: it returns to
    the caller's ra with fuzz_catalogue_row's a0. Level-3 identical in the two builds.
    It writes [sp - 16, sp) (its frame) and fuzz_catalogue_row's frame [sp - FCR_STACK, sp) (the tail call runs at
    the caller's sp): [sp - 48, sp).

    Post in the spine's terms: a0 = seg_spec.cat_ptr CAT (SegModel.by_token s): &fuzz_catalogue[i] for the first row i
    whose token is the string s, else 0 (pin_spec.row_ptr of the bytes is cat_ptr of SegModel.cat_row of their
    values: Spec/SegBridge.v and seg_spec.cat_tok_nth).

    Callee contracts its walk takes as premises: strlen_contract (Prog/strlen_c.v under lib/U, 0x1f5cc: the string, its NUL
    and the slack to the next 8-byte boundary) and fuzz_catalogue_row_contract (fuzz_catalogue_row_c.v,
    FUZZ_CATALOGUE_ROW = 0x166f4, FCR_STACK = 48: the table premise cat_img, the token outside [lo, sp)).

    Call site (reac_segconf_parse_file): 0x15924 `jal reac_box_catalogue_by_token` with a0 = low, the model
    fold buffer in parse_file's frame (sp + 0x190 of parse_file: at or above this sp), holding r_low val 0 24 and its
    NUL (at most 23 bytes; the slack up to the next 8-byte boundary lies in low[24] or the frame bytes after it, all
    present). The table reads as in the image by FR's relro (FrameAPI.frame_RELRO covers [sa_catalogue,
    sa_catalogue + CAT_BYTES)). *)
Definition REAC_BOX_CATALOGUE_BY_TOKEN : Z := 0x167a0.
Definition BY_TOKEN_STACK : Z := 48.

Definition by_token_pre (m : word -> option byte) (sp lo tok : Z) (s : list Z) : Prop :=
  tok <> 0 /\ cstr_at rsegs m tok s /\ apart tok (Z.of_nat (length s) + 1) lo sp /\
  stack_ok rsegs m lo sp BY_TOKEN_STACK /\ cat_img rsegs m (sa_catalogue SEG_UBSAN) /\ mem_inv rsegs m.

Definition reac_box_catalogue_by_token_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : list Z),
    by_token_pre m (bv_unsigned sp) lo (bv_unsigned a0) s ->
    evt rsegs
      (ret_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         (cat_ptr (sa_catalogue SEG_UBSAN) (by_token s))
         m
         ([(bv_unsigned sp - BY_TOKEN_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_CATALOGUE_BY_TOKEN) fc None m (seg_rom rsegs)).
