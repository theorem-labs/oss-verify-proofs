(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_libc_iface RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dmf_a RZ_dmf_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition zsep (x1 x2 y1 y2 : Z) : Prop := x2 <= y1 \/ y2 <= x1.
Definition zimp (P Q : Prop) : Prop := P -> Q.

Section DMFC.
  Variable TBL : tbl_pred.
  Hypothesis TBLL : tbl_laws TBL.
  Hypothesis DBLOCK : zd_dblock_stmt TBL.
  Hypothesis DBEGIN : zd_dbegin_stmt.
  Hypothesis CHECKCONT : zd_checkcont_stmt.
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis XXHRESET : zd_xxh_reset_stmt.
  Hypothesis GETCB : zd_getcblock_stmt.
  Hypothesis ERRCODE : zd_errcode_stmt.
  Hypothesis XXHUPD : zd_xxh_update_stmt.
  Hypothesis XXHDIG : zd_xxh_digest_stmt.
  Hypothesis MEMMOVE : zd_memmoveZ_stmt.
  Hypothesis MEMSET : zd_memsetZ_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z).
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 1099511627776.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 1099511627776.
  Hypothesis DNULL : zimp (DST = 0) (CAP = 0).  Hypothesis DNN : zimp (DST <> 0) (4096 <= DST).  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 2368.  Hypothesis RSP : SP < 2^47.  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis S_DC : zsep DCTX (DCTX + 95992) lo SP.
  Hypothesis S_DS : zsep DST (DST + CAP) lo SP.
  Hypothesis S_SR : zsep SRC (SRC + zlen src) lo SP.
  Hypothesis S_GT : zsep 0x36e40 (0x36e40 + 16) lo SP.
  Hypothesis D_DC : zsep DST (DST + CAP) DCTX (DCTX + 95992).
  Hypothesis D_SR : zsep DST (DST + CAP) SRC (SRC + zlen src).
  Hypothesis SR_DC : zsep SRC (SRC + zlen src) DCTX (DCTX + 95992).
  Hypothesis GT_DC : zsep 0x36e40 (0x36e40 + 16) DCTX (DCTX + 95992).
  Hypothesis GT_DS : zsep 0x36e40 (0x36e40 + 16) DST (DST + CAP).

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -272)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Notation frl_cells := (RZ_dmf_a.frl_cells DCTX DST).
  Notation frh_cells := (RZ_dmf_a.frh_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation ENV := (RZ_dmf_a.ENV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src).
  Notation A_INV := (RZ_dmf_a.A_INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP lo DCTX DST CAP SRC src size).
  Notation ASt mm off sz tot mt1 x1 x5 x8 x11 x12 x13 x14 x26 x27 x28 x29 x30 x31 :=
    (STpc 0x155a8 mm x1 x5 (Z_to_bv 64 (-120)) (Z_to_bv 64 25481893) x8 (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 5) x11 x12 x13 x14
          (Z_to_bv 64 5) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 sz) (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 0)
          (Z_to_bv 64 mt1) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 4294967287) (Z_to_bv 64 (DCTX + 29928)) x26 x27 x28 x29 x30 x31).


  Notation B_DCTX := (RZ_dmf_b.B_DCTX TBL DCTX).
  Notation FRAME_OK := (RZ_dmf_b.FRAME_OK CAP src size).
  Notation KA_T := (RZ_dmf_b.KA_T ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size).
  Notation FRLB mm mt1 sl0 sl1 sl2 := (rw_cells usegs mm (SP + -272) (frl_cells sl0 sl1 sl2 (Z_to_bv 64 mt1))).
  Notation B_HEAD := (RZ_dmf_b.B_HEAD TBL ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SP lo DCTX DST CAP SRC src size).

  Ltac sep_open :=
    pose proof S_DC as S_DC_; pose proof S_DS as S_DS_; pose proof S_SR as S_SR_; pose proof S_GT as S_GT_; pose proof D_DC as D_DC_;
    pose proof D_SR as D_SR_; pose proof SR_DC as SR_DC_; pose proof GT_DC as GT_DC_; pose proof GT_DS as GT_DS_;
    unfold zsep in S_DC_, S_DS_, S_SR_, S_GT_, D_DC_, D_SR_, SR_DC_, GT_DC_, GT_DS_.
  Ltac sep_close := repeat match goal with H : (_ <= _) \/ (_ <= _) |- _ => clear H end.

  (* [comment removed for export] *)
  Hypothesis L_errx : forall mm off sz tot mt1 res sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    zd_is_error res = true -> 0 <= res < 2^64 -> KA_T sz ->
    evt usegs POST (STpc 0x15764 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 res) (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).

  Hypothesis L_errx2 : forall mm off sz tot mt1 sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y24 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> dctx_any mm DCTX ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x15760 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                       (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 y24 (Z_to_bv 64 (DCTX + 29928))
                       y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).

  Hypothesis L_fend : forall mm off sz tot mt1 res ipE remE h PFX (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) xs ws sl0 sl1 sl2
      (y1 y5 y6 y7 y8 y10 y12 y14 y15 y16 y17 y18 y21 y23 y24 y26 y28 y29 y30 y31 : word),
    ENV mm -> FRLB mm mt1 sl0 sl1 sl2 -> B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    0 <= fh_checksum h <= 1 -> 0 <= fh_fcs h < 2^64 ->
    0 <= off -> off + sz <= size -> 0 <= tot <= CAP -> (mt1 = 0 \/ mt1 = 1) ->
    (forall r, dmulti src off sz (CAP - tot) tot r -> decompress_ok src size CAP r) ->
    0 <= res <= CAP - tot -> off <= ipE -> ipE + remE <= size -> 0 <= remE < sz ->
    (forall ipF remF, (if fh_checksum h =? 0 then ipF = ipE /\ remF = remE else 4 <= remE /\ ipF = ipE + 4 /\ remF = remE - 4) ->
        (fh_fcs h <> ZD_CONTENTSIZE_UNKNOWN -> res = fh_fcs h) ->
        forall r, dmulti src ipF remF (CAP - tot - res) (tot + res) r -> dmulti src off sz (CAP - tot) tot r) ->
    KA_T sz ->
    evt usegs POST (STpc 0x159b8 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 (Z_to_bv 64 remE) y12 (Z_to_bv 64 (DST + tot + res))
                       y14 y15 y16 y17 y18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 (Z_to_bv 64 (SRC + ipE)) y23 y24
                       (Z_to_bv 64 (DCTX + 29928)) y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31).

  Lemma B_DCTX_any : forall mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws -> dctx_any mm DCTX.
  Proof. exact (RZ_dmf_b.B_DCTX_any TBL DCTX). Qed.

  Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l hh] W IH]; cbn; intros a n a' n' D L1 L2; [exact I|].
    destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma B_DCTX_transport : forall W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    munch W' m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m1 -> mem_inv usegs m2 ->
    disjoint_from W' DCTX 95992 ->
    B_DCTX m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws.
  Proof.
    intros W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
           (PT & H1 & FP & H3 & [XSC XSSZ] & XSI & [H5C H5L] & H5OK & K_VCK & K_ISF & (jhb & ovd & dcb & dce & trace & TX) & [OWE OWX] & TB)
           MU WM MI1 MI2 DJ.
    assert (TR : forall A cs, rw_cells usegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells usegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
    assert (TS : forall a b, stk usegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk usegs m2 a b).
    { intros a b SK L1 L2 L3. eapply stk_transport_disjoint; [exact SK | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ | lia | lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_xs, dctx_h5, dctx_tx, dctx_owned in *.
    split; [apply TR; [exact PT | lia | cbn; lia]|].
    split; [apply TR; [exact H1 | lia | cbn; lia]|].
    split; [apply TR; [exact FP | lia | cbn; lia]|].
    split; [apply TR; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
    split; [exact XSI|].
    split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|]. split; [exact K_VCK|]. split; [exact K_ISF|].
    split; [exists jhb, ovd, dcb, dce, trace; apply TR; [exact TX | lia | cbn; lia]|].
    split; [split; apply TS; try assumption; lia|].
    eapply (tbl_frame TBL TBLL m1 m2 W'); [exact TB | exact MU | exact MI1 | exact MI2 |].
    intros x Hx. eapply disjoint_outside; [exact DJ | lia].
  Qed.

  (* [comment removed for export] *)
  Definition B_NOXS (m1 : fmem) (h : frame_header) (PFX : Z) (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (ws : list word) : Prop :=
    dctx_ptrs usegs m1 DCTX llt mlt oft huf /\
    dctx_h1 usegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd /\
    rw_cells usegs m1 (DCTX + 29928) (zfh_cells h) /\
    dctx_h3 usegs m1 DCTX pcs dsz bt stg le fe /\
    dctx_h5 usegs m1 DCTX ws /\ h5_frame_ok ws /\
    wnth ws H5_validateChecksum = Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1) /\
    wnth ws H5_isFrameDecompression = Z_to_bv 64 1 /\
    (exists jhb ovd dcb dce trace, dctx_tx usegs m1 DCTX jhb ovd dcb dce trace) /\
    dctx_owned usegs m1 DCTX /\
    TBL m1 DCTX llt mlt oft huf le fe.

  Lemma B_DCTX_split : forall m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_DCTX m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    B_NOXS m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws.
  Proof.
    intros m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws (A1 & A2 & A3 & A4 & _ & _ & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma B_DCTX_join : forall m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws,
    B_NOXS m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws ->
    dctx_xs usegs m1 DCTX xs -> (fh_checksum h <> 0 -> exists j1 msz j2, xs = xxh_cells j1 msz j2 /\ 0 <= msz < 32) ->
    B_DCTX m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws.
  Proof.
    intros m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) X1 X2.
    repeat (split; [assumption|]). assumption.
  Qed.

  Lemma B_NOXS_transport : forall W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws,
    B_NOXS m1 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws ->
    munch W' m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m1 -> mem_inv usegs m2 ->
    disjoint_from W' DCTX 30008 -> disjoint_from W' (DCTX + 30096) 65896 ->
    B_NOXS m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws.
  Proof.
    intros W' m1 m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe ws
           (PT & H1 & FP & H3 & [H5C H5L] & H5OK & K_VCK & K_ISF & (jhb & ovd & dcb & dce & trace & TX) & [OWE OWX] & TB)
           MU WM MI1 MI2 DJ1 DJ2.
    assert (TR1 : forall A cs, rw_cells usegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 30008 -> rw_cells usegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ1 | lia | lia]. }
    assert (TR2 : forall A cs, rw_cells usegs m1 A cs -> DCTX + 30096 <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells usegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_transport; [exact RC | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ2 | lia | lia]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_h5, dctx_tx, dctx_owned in *.
    split; [apply TR1; [exact PT | lia | cbn; lia]|].
    split; [apply TR1; [exact H1 | lia | cbn; lia]|].
    split; [apply TR1; [exact FP | lia | cbn; lia]|].
    split; [apply TR1; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR2; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|]. split; [exact K_VCK|]. split; [exact K_ISF|].
    split; [exists jhb, ovd, dcb, dce, trace; apply TR2; [exact TX | lia | cbn; lia]|].
    split; [split|].
    - eapply stk_transport_disjoint; [exact OWE | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ1 | lia | lia].
    - eapply stk_transport_disjoint; [exact OWX | exact MU | exact WM |]. eapply disjoint_from_sub; [exact DJ2 | lia | lia].
    - eapply (tbl_frame TBL TBLL m1 m2 W'); [exact TB | exact MU | exact MI1 | exact MI2 |].
      intros x Hx. eapply disjoint_outside; [exact DJ1 | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dj_atom := first [ left; lia | right; lia | lia ].
  Ltac dj_one :=
    first [ dj_atom
          | match goal with S : zsep _ _ _ _ |- _ =>
              let S' := fresh "S'" in pose proof S as S'; unfold zsep in S'; destruct S' as [S'|S']; dj_atom end ].
  Ltac dj_solve := cbn [disjoint_from]; simpl_sizes; repeat split; first [ exact I | dj_one ].

  Ltac bdctx_transport segs m m' MU WM MI' :=
    repeat match goal with
    | H : B_DCTX m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        first [ eapply (B_DCTX_transport _ m m') in H;
                  [ | exact MU | exact WM | match goal with MI0 : mem_inv segs m |- _ => exact MI0 end | exact MI' | dj_solve ]
              | idtac "note: dropping B_DCTX (not provably disjoint from callee footprint):" H; clear H ]
    | H : B_NOXS m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        first [ eapply (B_NOXS_transport _ m m') in H;
                  [ | exact MU | exact WM | match goal with MI0 : mem_inv segs m |- _ => exact MI0 end | exact MI' | dj_solve | dj_solve ]
              | idtac "note: dropping B_NOXS (not provably disjoint from callee footprint):" H; clear H ]
    end.
  (* [comment removed for export] *)
  Ltac zd_transport segs m m' MU WM :=
    let W := lazymatch type of MU with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at segs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
    | H : rw_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : ro_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
              | idtac "note: dropping stk (not provably disjoint from callee footprint):" H; clear H ]
    | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
    end.
  Ltac post_callk segs m :=
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO;
    destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
    destruct PO as [E [MUc [WMc PO]]];
    first [ destruct PO as [MIc PO] | rename PO into MIc ];
    subst ms';
    lazymatch type of MUc with
    | munch ?Wc m ?m' =>
        bdctx_transport segs m m' MUc WMc MIc;
        (* [comment removed for export] *)
        repeat match goal with
        | H : munch ?Wq ?mq m |- _ =>
            let SF := fresh "SF" in
            assert (SF : sub_fp Wc Wq) by (first [ eassumption | unfold sub_fp; cbn [outside]; intros; slia ]);
            apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken Wc Wq m m'); [ exact SF | exact MUc ] ]; clear SF
        end;
        zd_transport segs m m' MUc WMc;
        clear MUc WMc;
        try match goal with H : mem_inv segs m |- _ => clear H end;
        try clear m
    end;
    try destruct_ands PO;
    try (lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end).
  Tactic Notation "callk" uconstr(SPEC) :=
    lazymatch goal with
    | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callk segs m ]
    end.

  (* [comment removed for export] *)
  Definition BLK_OK (off sz tot hsz PFX ipb rem o cbs : Z) (bp : block_props) : Prop :=
    ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) /\
    off + hsz <= ipb /\ ipb + rem <= off + sz /\ 0 <= o <= CAP - tot /\
    get_cblock_size src ipb rem = Some (cbs, bp) /\ zd_is_error cbs = false /\ cbs <= rem - 3 /\
    (forall ip' rem' o', dblocks src (CAP - tot) ipb rem o ip' rem' o' -> dblocks src (CAP - tot) (off + hsz) (sz - hsz) 0 ip' rem' o').

  (* [comment removed for export] *)
  Lemma L_after2 : forall mm off sz tot mt1 hsz h PFX ipb rem o cbs bp v
      (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31 : word),
    ENV mm -> FRLB mm mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs mm (SP + -168) (bp_cells bp) ->
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp ->
    block_result (CAP - tot - o) cbs bp v -> 0 <= v ->
    KA_T sz ->
    (bp_last bp = 0 -> B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evt usegs POST (STpc 0x15950 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + (ipb + 3)))
                         x23 (Z_to_bv 64 v) (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31
           ENm FRLm BPXm BDm (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH) (WIN & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK) BRm RVm KA KB.
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & CNRLE). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in *.
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & RFCS & _ & _ & _ & RCK & _).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    assert (RV2 : v <= CAP - tot - o).
    { unfold block_result in BRm. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia. }

    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof BPXm as BPXm'. unfold bp_cells in BPXm'.
    pose proof ENm as (GOTm & SBm & DSKm & _ & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof DSKm as (DST0 & _ & _).
    pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
    pose proof DNULL as DN1. unfold zimp in DN1.
    assert (JOIN : forall w8 : word,
      evt usegs POST (STpc 0x1596c mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) x10 x11 x12 (Z_to_bv 64 (DST + tot + (o + v)))
                           x14 x15 x16 x17 x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + (ipb + 3)))
                           x23 w8 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31)).
    { intros w8.
    zs. zs. rewrite zb_lxor_ones by lia. fck. zs. rewrite sx32w_small by lia. zs. zs. zs. zs. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      replace (SRC + (ipb + 3) + cbs) with (SRC + (ipb + 3 + cbs)) by lia.
      replace (rem + -3 - cbs) with (rem - 3 - cbs) by lia.
      eapply (L_fend mm off sz tot mt1 (o + v) (ipb + 3 + cbs) (rem - 3 - cbs) h PFX); try eassumption; try lia.
      intros ipF remF CKC FCSC r DM.
      eapply (DM_frame src off sz (CAP - tot) tot r (o + v) ipF remF); [unfold ZD_FRAMEHEADERSIZE_PREFIX; lia | exact NSK | | exact DM].
      unfold dframe. split; [unfold ZD_FRAMEHEADERSIZE_MIN, ZD_blockHeaderSize; lia|]. cbv zeta. rewrite <- EHSZ.
      split; [unfold ZD_blockHeaderSize; lia|].
      exists h, (ipb + 3 + cbs), (rem - 3 - cbs). split; [exact GFH|].
      split. { apply DBK. apply (DB_last src (CAP - tot) ipb rem o cbs bp v GCB NEC); [unfold ZD_blockHeaderSize; lia | exact BRm | exact KL]. }
      split; [exact FCSC|].
      destruct (fh_checksum h =? 0); [destruct CKC; split; assumption| destruct CKC as (C1 & C2 & C3); split; [exact C1|]; split; assumption].
    - (* [comment removed for export] *)
      assert (MU3 : munch [(SP + -272, SP + -168)] mm mm) by apply munch_refl.
      assert (WM3 : wmono usegs mm mm) by apply wmono_refl.
      pose proof MIm as MIm0.
      pose proof S_SR as S_SR_; pose proof S_GT as S_GT_; unfold zsep in S_SR_, S_GT_. zs. clear S_SR_ S_GT_.
      lazymatch type of MU3 with munch _ _ ?m2 =>
        assert (BD2 : B_DCTX m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
          by (eapply (B_DCTX_transport _ mm m2); [exact BDm | exact MU3 | exact WM3 | eassumption | eassumption | dj_solve])
      end.
      clear BDm ENm MU3 WM3.
      zs. zs. zs.
      unfold PZD_GETCBLOCK in GETCB.
      assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
      zs.
      callk (GETCB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SRC (SP + -168) src (ipb + 3 + cbs) (rem - 3 - cbs) _);
        [ exact SBm | exact OK | lia | lia | lia | lia | exact BPXm' | reflexivity | lia | lia | eassumption | f_equal; lia | f_equal; lia | f_equal; lia | ].
      assert (ENx : ENV x8).
      { split; [exact GOTm|]. split; [exact SBm|]. split; [exact DSKm|]. split; [exists x9; split; [exact PC| exact PC0]|].
        split; [exists jt; exact FRHm|]. split; [exact STm|]. split; [exact MUm|]. split; [exact WMm| exact MI]. }
      pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BD2) as DAx.
      set (ip2 := ipb + 3 + cbs) in *. set (rem2 := rem - 3 - cbs) in *.
      assert (RRET : 0 <= cblock_ret (get_cblock_size src ip2 rem2) < 18446744073709551616).
      { clear - OK. unfold get_cblock_size.
        destruct (rem2 <? ZD_blockHeaderSize); cbn [cblock_ret].
        - unfold ZERR, ZE_srcSize_wrong. change (2^64) with 18446744073709551616. lia.
        - pose proof (cblock_props_range (le24 src ip2) (le24_range src OK ip2)) as (_ & _ & RO2). change (2^21) with 2097152 in RO2.
          unfold bt_rle, bt_reserved, ZERR, ZE_corruption_detected. change (2^64) with 18446744073709551616.
          destruct (_ =? 1); [lia|]. destruct (_ =? 3); lia. }
      zs. zs. zs. zs. if_cases KE; zify_cond KE.
      + (* [comment removed for export] *)
        destruct (get_cblock_size src ip2 rem2) as [[v2 bp2]|] eqn:G2; cbn [cblock_ret] in *;
          [| exfalso; unfold ZERR, ZE_srcSize_wrong in KE; change (2^64) with 18446744073709551616 in KE; lia].
        rewrite (POST v2 bp2 eq_refl) in PC.
        replace (SRC + (ipb + 3) + cbs) with (SRC + ip2) by (unfold ip2; lia).
        replace (rem + -3 - cbs) with rem2 by (unfold rem2; lia).
        eapply (KB KL x8 v2 bp2); try eassumption.
        apply zd_is_error_false_iff. change (2^64) with 18446744073709551616. lia.
      + (* [comment removed for export] *)
        zs.
        eapply (L_errx x8 off sz tot mt1 (cblock_ret (get_cblock_size src ip2 rem2))); try eassumption.
        apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
    }
    zs. zs. if_cases KV; zify_cond KV.
    - replace (DST + tot + o) with (DST + tot + (o + v)) by lia. apply JOIN.
    - zs. zs. fck. zs. fck. zs. fck. zs.
      match goal with |- context [Z_to_bv 64 (v + (DST + tot + o))] =>
        replace (v + (DST + tot + o)) with (DST + tot + (o + v)) by lia end.
      apply JOIN.
  Qed.

  (* [comment removed for export] *)
  Lemma L_after : forall mm off sz tot mt1 hsz h PFX ipb rem o cbs bp v
      (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31 : word),
    ENV mm -> FRLB mm mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs mm (SP + -168) (bp_cells bp) ->
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp ->
    block_result (CAP - tot - o) cbs bp v -> 0 <= v ->
    KA_T sz ->
    (bp_last bp = 0 -> B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evt usegs POST (STpc 0x15938 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + (ipb + 3)))
                         x23 (Z_to_bv 64 v) (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX ipb rem o cbs bp v llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0
           x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31
           ENm FRLm BPXm BDm FOK BOK BRm RVm KA KB.
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof BOK as (_ & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & _ & _ & _ & _ & RCK & _).
    assert (RV2 : v <= CAP - tot - o).
    { unfold block_result in BRm. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia. }
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof ENm as (GOTm & SBm & DSKm & (csb & BPCm & BSZm) & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof BDm as (_ & _ & _ & _ & [XSCm XSSZm] & XSIm & [H5Cm H5Lm] & _ & K_VCKm & _).
    destruct (Z.eqb_spec (fh_checksum h) 0) as [ECK|ECK].
    - (* [comment removed for export] *)
      h5_open ws H5Lm. subst b2.
      zs. rewrite sx32w_small by lia. zs. if_true.
      eapply (L_after2 mm off sz tot mt1 hsz h PFX ipb rem o cbs bp v); try eassumption.
    - destruct (XSIm ECK) as (j1 & msz & j2 & -> & RMSZ). unfold xxh_cells in XSCm.
      apply B_DCTX_split in BDm.
      h5_open ws H5Lm. subst b2.
      zs. rewrite sx32w_small by lia. zs. if_false. zs. zs. zs. zs.
      assert (INB : exists inb, bytes_at usegs mm (DST + tot + o) inb /\ zlen inb = v).
      { destruct (stk_split usegs mm DST (DST + tot + o) (DST + CAP) DSKm ltac:(lia)) as [_ S2].
        destruct (stk_split usegs mm (DST + tot + o) (DST + tot + o + v) (DST + CAP) S2 ltac:(lia)) as [S3 _].
        destruct (stk_bytes usegs mm _ _ S3 ltac:(lia)) as (inb & LINB & BINB).
        exists inb. split; [exact BINB|]. rewrite LINB. lia. }
      destruct INB as (inb & BINB & LINB).
      pose proof BPXm as BPXm'. unfold bp_cells in BPXm'. unfold RZ_dmf_a.frh_cells in FRHm.
      assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
      unfold PZD_XXH_UPDATE in XXHUPD.
      pose proof DNULL as DN1. pose proof DNN as DN2. unfold zimp in DN1, DN2.
      pose proof S_DC as SEPX1. pose proof S_DS as SEPX2. pose proof D_DC as SEPX3. unfold zsep in SEPX1, SEPX2, SEPX3.
      callk (XXHUPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) (DCTX + 30008) (DST + tot + o) inb msz lo);
        [ exists j1, j2; exact XSCm | exact RMSZ | lia | lia | lia
        | destruct (Z.eq_dec DST 0) as [D0|D0]; [left; split; [lia | f_equal; lia] | right; split; [exact BINB|]; split; [rewrite LINB; reflexivity|]; lia]
        | exact STm | lia | lia | lia | lia | exact MIm | reflexivity | reflexivity | ].
      clear DN1 DN2 SEPX1 SEPX2 SEPX3.
      lazymatch goal with
      | H : xxh_state ?mx _ ?mz |- _ =>
          destruct H as (j1' & j2' & XS2);
          assert (ENx : ENV mx)
            by (split; [exact GOTm|]; split; [exact SBm|]; split; [exact DSKm|]; split; [exists csb; split; [exact BPCm| exact BSZm]|];
                split; [exists jt; exact FRHm|]; split; [eassumption|]; split; [exact MUm|]; split; [exact WMm| eassumption]);
          assert (XSI2 : fh_checksum h <> 0 -> exists j3 msz0 j4, xxh_cells j1' mz j2' = xxh_cells j3 msz0 j4 /\ 0 <= msz0 < 32)
            by (intros _; exists j1', mz, j2'; split; [reflexivity| lia]);
          pose proof (B_DCTX_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm (conj XS2 eq_refl) XSI2) as BDx;
          eapply (L_after2 mx off sz tot mt1 hsz h PFX ipb rem o cbs bp v); try eassumption
      end.
  Qed.

  (* [comment removed for export] *)
  Lemma L_raw : forall mm off sz tot mt1 hsz h PFX ipb rem o cbs bp
      (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 : word)
      (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31 : word),
    ENV mm -> FRLB mm mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs mm (SP + -168) (bp_cells bp) ->
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp ->
    bp_type bp = bt_raw ->
    KA_T sz ->
    (forall v, block_result (CAP - tot - o) cbs bp v -> 0 <= v -> bp_last bp = 0 -> B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evt usegs POST (STpc 0x15904 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) x10 x11 x12 (Z_to_bv 64 (DST + tot + o))
                         x14 x15 x16 x17 x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + (ipb + 3)))
                         x23 x24 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX ipb rem o cbs bp llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0
           x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31
           ENm FRLm BPXm BDm FOK BOK TRAW KA KB.
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof BOK as (_ & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & CNRLE). change (2^21) with 2097152 in *.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof ENm as (GOTm & SBm & DSKm & (csb & BPCm & BSZm) & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    assert (ERR : forall code (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 : word), 0 < code < ZE_maxCode ->
      evt usegs POST (STpc 0x15764 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                         (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 (ZERR code)) (Z_to_bv 64 (DCTX + 29928))
                         y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31)).
    { intros code y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 RCODE.
      eapply (L_errx mm off sz tot mt1 (ZERR code)); try eassumption.
      - apply zd_is_error_ZERR. lia.
      - unfold ZERR, ZE_maxCode in *. lia. }
    zs. replace (DST + CAP - (DST + tot + o)) with (CAP - tot - o) by lia.
    zs. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zs. zs.
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (ZERR ZE_dstSize_tooSmall)) by (apply Z_to_bv_eqm; reflexivity).
      apply ERR. unfold ZE_dstSize_tooSmall, ZE_maxCode. lia.
    - zs. if_cases KN; zify_cond KN.
      + (* [comment removed for export] *)
        zs. if_cases KZ; zify_cond KZ.
        * zs. zs.
          replace (Z_to_bv 64 (-74)) with (Z_to_bv 64 (ZERR ZE_dstBuffer_null)) by (apply Z_to_bv_eqm; reflexivity).
          apply ERR. unfold ZE_dstBuffer_null, ZE_maxCode. lia.
        * zs.
          eapply (L_after mm off sz tot mt1 hsz h PFX ipb rem o cbs bp 0); try eassumption; try lia.
          -- unfold block_result. rewrite TRAW. cbn. lia.
          -- intros KL. apply (KB 0); [unfold block_result; rewrite TRAW; cbn; lia | lia | exact KL].
      + (* [comment removed for export] *)
        pose proof DSKm as (DST0 & _ & _).
        destruct (stk_split usegs mm DST (DST + tot + o) (DST + CAP) DSKm ltac:(lia)) as [SK1 SK23].
        destruct (stk_split usegs mm (DST + tot + o) (DST + tot + o + cbs) (DST + CAP) SK23 ltac:(lia)) as [SK2 SK3].
        clear DSKm SK23.
        pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as RHS.
        rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
        assert (RDS : rdbl usegs mm (SRC + (ipb + 3)) (SRC + (ipb + 3) + cbs)).
        { eapply rdbl_sub; [apply (rdbl_of_bytes_at usegs _ _ _ SBm) | lia | rewrite length_map; lia]. }
        pose proof BPXm as BPXm'. unfold bp_cells in BPXm'. unfold RZ_dmf_a.frh_cells in FRHm.
        assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
        pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
        zs. zs. zs. zs.
        clear FRLm BPXm ENm DAm.
        assert (SK2' : id (stk usegs mm (DST + tot + o) (DST + tot + o + cbs))) by exact SK2. clear SK2.
        assert (SUBFP : sub_fp [(DST + tot + o, DST + tot + o + cbs)] W).
        { clear - RT RO KR RCBS. unfold sub_fp. cbn [outside]. intros x Hx. split; [lia| exact I]. }
        callk (MEMMOVE (DST + tot + o) (SRC + (ipb + 3)) cbs);
          [ exact SK2' | exact RDS | lia | lia | lia | change (2^63) with 9223372036854775808; lia | change (2^63) with 9223372036854775808; lia
          | exact MIm | reflexivity | reflexivity | reflexivity | ].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (DSKx : stk usegs mx DST (DST + CAP))
            by (eapply stk_merge; [eapply stk_merge; [exact SK1 | exact POST | lia] | exact SK3 | lia]);
          assert (ENx : ENV mx)
            by (split; [exact GOTm|]; split; [exact SBm|]; split; [exact DSKx|]; split; [exists csb; split; [exact BPCm| exact BSZm]|];
                split; [exists jt; exact FRHm|]; split; [exact STm|]; split; [exact MUm|]; split; [exact WMm| exact MI])
        end.
        zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (L_after mx off sz tot mt1 hsz h PFX ipb rem o cbs bp cbs); try eassumption; try lia end.
        -- unfold block_result. rewrite TRAW. cbn. lia.
        -- intros KL. apply (KB cbs); [unfold block_result; rewrite TRAW; cbn; lia | lia | exact KL].
  Qed.

  (* [comment removed for export] *)
  Lemma L_rle : forall mm off sz tot mt1 hsz h PFX ipb rem o cbs bp rm
      (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 : word)
      (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31 : word),
    ENV mm -> FRLB mm mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs mm (SP + -168) (bp_cells bp) ->
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp ->
    bp_type bp = bt_rle -> 0 <= rm <= CAP - tot - o ->
    KA_T sz ->
    (forall v, block_result (CAP - tot - o) cbs bp v -> 0 <= v -> bp_last bp = 0 -> B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evt usegs POST (STpc 0x158b4 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 (DST + tot + o + rm)) x11 x12
                         (Z_to_bv 64 (DST + tot + o)) x14 x15 x16 x17 x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs)
                         (Z_to_bv 64 (SRC + (ipb + 3))) x23 x24 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX ipb rem o cbs bp rm llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0
           x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31
           ENm FRLm BPXm BDm FOK BOK TRLE RRM KA KB.
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof BOK as (_ & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & CRLE & _). change (2^21) with 2097152 in *. specialize (CRLE TRLE).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof BPXm as BPXm'. unfold bp_cells in BPXm'.
    pose proof ENm as (GOTm & SBm & DSKm & (csb & BPCm & BSZm) & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof DSKm as (DST0 & _ & _).
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    assert (ERR : forall code (y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 : word), 0 < code < ZE_maxCode ->
      evt usegs POST (STpc 0x15764 mm y1 y5 y6 y7 y8 (Z_to_bv 64 (DST + tot)) y10 y11 y12 y13 y14 y15 y16 y17 y18
                         (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) y21 y22 y23 (Z_to_bv 64 (ZERR code)) (Z_to_bv 64 (DCTX + 29928))
                         y26 (Z_to_bv 64 (-72)) y28 y29 y30 y31)).
    { intros code y1 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y22 y23 y26 y28 y29 y30 y31 RCODE.
      eapply (L_errx mm off sz tot mt1 (ZERR code)); try eassumption.
      - apply zd_is_error_ZERR. lia.
      - unfold ZERR, ZE_maxCode in *. lia. }
    zs. rewrite zx32w_small by lia.
    zs. replace (DST + tot + o + rm - (DST + tot + o)) with rm by lia.
    zs. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zs. zs.
      replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (ZERR ZE_dstSize_tooSmall)) by (apply Z_to_bv_eqm; reflexivity).
      apply ERR. unfold ZE_dstSize_tooSmall, ZE_maxCode. lia.
    - zs. if_cases KN; zify_cond KN.
      + (* [comment removed for export] *)
        zs. if_cases KZ; zify_cond KZ.
        * rewrite KZ.
          eapply (L_after mm off sz tot mt1 hsz h PFX ipb rem o cbs bp 0); try eassumption; try lia.
          -- unfold block_result. rewrite TRLE. cbn. lia.
          -- intros KL. apply (KB 0); [unfold block_result; rewrite TRLE; cbn; lia | lia | exact KL].
        * zs. zs. zs.
          replace (Z_to_bv 64 (-74)) with (Z_to_bv 64 (ZERR ZE_dstBuffer_null)) by (apply Z_to_bv_eqm; reflexivity).
          apply ERR. unfold ZE_dstBuffer_null, ZE_maxCode. lia.
      + (* [comment removed for export] *)
        destruct (stk_open usegs mm DST (DST + CAP) (DST + tot + o) (Z.to_nat (bp_orig bp)) DSKm ltac:(lia) ltac:(lia)) as (jd & DCB & SK1 & SK3).
        rewrite Z2Nat.id in SK3 by lia.
        clear DSKm.
        unfold RZ_dmf_a.frh_cells in FRHm.
        assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
        pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
        zlb SBm OK (ipb + 3).
        zs. zs. zs.
        clear FRLm BPXm ENm DAm.
        assert (DCB' : id (rw_cells usegs mm (DST + tot + o) [CB (Z.to_nat (bp_orig bp)) jd])) by exact DCB. clear DCB.
        assert (SUBFP : sub_fp [(DST + tot + o, DST + tot + o + bp_orig bp)] W).
        { clear - RT RO KR RRM RBO. unfold sub_fp. cbn [outside]. intros x Hx. split; [lia| exact I]. }
        callk (MEMSET (DST + tot + o) (bp_orig bp) (Znth (ipb + 3) src));
          [ exact DCB' | exact MIm | reflexivity | reflexivity | reflexivity | lia | change (2^64) with 18446744073709551616; lia | change (2^64) with 18446744073709551616; lia | ].
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (DSKx : stk usegs mx DST (DST + CAP))
            by (eapply (stk_close usegs mx DST (DST + CAP) (DST + tot + o)); [exact SK1 | exact POST | | lia |];
                cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; [exact SK3 | lia]);
          assert (ENx : ENV mx)
            by (split; [exact GOTm|]; split; [exact SBm|]; split; [exact DSKx|]; split; [exists csb; split; [exact BPCm| exact BSZm]|];
                split; [exists jt; exact FRHm|]; split; [exact STm|]; split; [exact MUm|]; split; [exact WMm| exact MI])
        end.
        zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          eapply (L_after mx off sz tot mt1 hsz h PFX ipb rem o cbs bp (bp_orig bp)); try eassumption; try lia end.
        -- unfold block_result. rewrite TRLE. cbn. lia.
        -- intros KL. apply (KB (bp_orig bp)); [unfold block_result; rewrite TRLE; cbn; lia | lia | exact KL].
  Qed.

  (* [comment removed for export] *)
  Lemma L_cmp : forall mm off sz tot mt1 hsz h PFX ipb rem o cbs bp rm
      (llt mlt oft huf pde expd pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (sl0 : word)
      (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31 : word),
    ENV mm -> FRLB mm mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) -> rw_cells usegs mm (SP + -168) (bp_cells bp) ->
    B_DCTX mm h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
    FRAME_OK off sz tot mt1 hsz h -> BLK_OK off sz tot hsz PFX ipb rem o cbs bp ->
    bp_type bp = bt_compressed -> 0 <= rm <= CAP - tot - o ->
    KA_T sz ->
    (forall v, block_result (CAP - tot - o) cbs bp v -> 0 <= v -> bp_last bp = 0 -> B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)) ->
    evt usegs POST (STpc 0x158d8 mm x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) (Z_to_bv 64 (DST + tot + o + rm)) x11 x12
                         (Z_to_bv 64 (DST + tot + o)) x14 x15 x16 x17 x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs)
                         (Z_to_bv 64 (SRC + (ipb + 3))) x23 x24 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31).
  Proof.
    intros mm off sz tot mt1 hsz h PFX ipb rem o cbs bp rm llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws sl0
           x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31
           ENm FRLm BPXm BDm FOK BOK TCMP RRM KA KB.
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof BOK as (WIN & RI1 & RI2 & RO & GCB & NEC & KFIT & DBK).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & _ & _). change (2^21) with 2097152 in *.
    pose proof (get_frame_header_ok src OK off hsz h GFH) as (_ & _ & _ & _ & RWIN & RBSM & _).
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof BPXm as BPXm'. unfold bp_cells in BPXm'.
    pose proof ENm as (GOTm & SBm & DSKm & (csb & BPCm & BSZm) & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof DSKm as (DST0 & _ & _). unfold RZ_dmf_a.frh_cells in FRHm.
    destruct BDm as (PT & H1 & FP & H3 & [XSC XSSZ] & XSI & H5 & H5OK & K_VCK & K_ISF & (jhb & ovd & dcb & dce & trace & TX) & OWN & TB).
    unfold dctx_h1, dctx_tx in H1, TX. pose proof FP as FP'. unfold zfh_cells in FP'.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
    zs. replace (DST + tot + o + rm - (DST + tot + o)) with rm by lia.
    zs. zs. zs. zs. zs. zs.
    clear FRLm BPXm ENm FP.
    assert (PT' : id (dctx_ptrs usegs mm DCTX llt mlt oft huf)) by exact PT. clear PT.
    assert (H3' : id (dctx_h3 usegs mm DCTX pcs dsz bt stg le fe)) by exact H3. clear H3.
    assert (H5' : id (dctx_h5 usegs mm DCTX ws)) by exact H5. clear H5.
    assert (OWN' : id (dctx_owned usegs mm DCTX)) by exact OWN. clear OWN.
    assert (DSK' : id (stk usegs mm DST (DST + CAP))) by exact DSKm. clear DSKm.
    assert (H1' : id (dctx_h1 usegs mm DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd)) by exact H1.
    assert (FPz : id (rw_cells usegs mm (DCTX + 29928) (zfh_cells h))) by exact FP'.
    assert (SUBFP : sub_fp [(DST + tot + o, DST + tot + o + rm); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940);
                            (SP + -272 - 2048, SP + -272)] W).
    { clear - RT RO RRM. unfold sub_fp. cbn [outside]. intros x Hx. repeat split; try lia; exact I. }
    assert (WINP : (PFX = 0 /\ rm = 0) \/ DST <= PFX <= DST + tot + o) by (clear - WIN RT RO RRM; lia).
    assert (NUL1 : DST + tot + o = 0 -> rm = 0) by (clear - DNULL RT RO RRM DST0; unfold zimp in DNULL; lia).
    assert (NUL2 : DST + tot + o <> 0 -> 4096 <= DST) by (clear - DNULL DNN RT RO RRM DST0; unfold zimp in *; lia).
    clear WIN.
    unfold PZD_DBLOCK in DBLOCK.
    callk (DBLOCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -272) lo DCTX (DST + tot + o) rm DST (DST + CAP) PFX SRC src (ipb + 3) cbs h
                       llt mlt oft huf pde expd pcs dsz bt stg le fe ws);
      [ exact PT' | exact H1' | exact FPz | unfold ZD_BLOCKSIZE_MAX in RBSM; lia | exact RWIN | exact H3' | exact H5' | exact K_ISF | exact OWN' | exact TB
      | exact RD0 | exact RD1 | exact RD8
      | exact SBm | exact OK | lia | change (2^21) with 2097152; lia | lia | exact RS0 | exact RS1
      | exact DSK' | lia | lia | lia | exact RDST
      | exact WINP | exact NUL1 | exact NUL2
      | exact STm | exact RLO | lia | lia
      | generalize S_DC; unfold zsep; lia | generalize S_DS; unfold zsep; lia | generalize S_SR; unfold zsep; lia | exact D_DC | exact D_SR | exact SR_DC
      | lia | exact MIm | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
    assert (ENx : ENV x26).
    { split; [exact GOTm|]. split; [exact SBm|]. split; [exact PC0|]. split; [exists csb; split; [exact BPCm| exact BSZm]|].
      split; [exists jt; exact FRHm|]. split; [exact PC|]. split; [exact MUm|]. split; [exact WMm| exact MI]. }
    assert (H5OKx : h5_frame_ok x38) by (exact (RZ_dmf_b.h5_frame_ok_keep ws x38 H5OK PC4)).
    assert (DAx : dctx_any x26 DCTX).
    { exists x32, x33, x34, x35, pde, (Z_to_bv 64 PFX), (Z_to_bv 64 PFX), (Z_to_bv 64 0), expd, (zfh_cells h), pcs, dsz, bt, stg, x36, x37, xs, x38, jhb, ovd, dcb, dce, trace.
      split; [exact PC1|]. split; [exact H1|]. split; [split; [exact FP'| reflexivity]|]. split; [exact PC2|]. split; [split; [exact XSC| exact XSSZ]|].
      split; [exact PC3|]. split; [exact H5OKx|]. split; [exact TX| exact PC5]. }
    change (2^64) with 18446744073709551616 in PC7.
    zs. zs. zs. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      assert (NE : zd_is_error x27 = false) by (apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
      assert (RV : x27 <= rm) by (destruct POST as [E|E]; [rewrite NE in E; discriminate E| exact E]).
      assert (BDx : B_DCTX x26 h PFX x32 x33 x34 x35 pde expd pcs dsz bt stg x36 x37 xs x38).
      { split; [exact PC1|]. split; [exact H1|]. split; [exact FP'|]. split; [exact PC2|]. split; [split; [exact XSC| exact XSSZ]|].
        split; [exact XSI|]. split; [exact PC3|]. split; [exact H5OKx|].
        split; [rewrite (PC4 H5_validateChecksum eq_refl); exact K_VCK|].
        split; [rewrite (PC4 H5_isFrameDecompression eq_refl); exact K_ISF|].
        split; [exists jhb, ovd, dcb, dce, trace; exact TX|]. split; [exact PC5| exact (PC6 NE)]. }
      eapply (L_after x26 off sz tot mt1 hsz h PFX ipb rem o cbs bp x27); try eassumption; try lia.
      + unfold block_result. rewrite TCMP. cbn. lia.
      + intros KL. apply (KB x27); [unfold block_result; rewrite TCMP; cbn; lia | lia | exact KL].
    - (* [comment removed for export] *)
      zs.
      eapply (L_errx x26 off sz tot mt1 x27); try eassumption.
      apply zd_is_error_true_iff. change (2^64) with 18446744073709551616. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_blocks : forall (n : nat) off sz tot mt1 hsz h PFX ipb rem o,
    rem <= Z.of_nat n ->
    FRAME_OK off sz tot mt1 hsz h ->
    ((PFX = 0 /\ CAP - tot = 0) \/ PFX = DST + tot) ->
    off + hsz <= ipb -> ipb + rem <= off + sz -> 0 <= o <= CAP - tot ->
    (forall ip' rem' o', dblocks src (CAP - tot) ipb rem o ip' rem' o' -> dblocks src (CAP - tot) (off + hsz) (sz - hsz) 0 ip' rem' o') ->
    KA_T sz ->
    B_HEAD off sz tot mt1 h PFX ipb rem o.
  Proof.
    induction n as [|n IH]; intros off sz tot mt1 hsz h PFX ipb rem o RN FOK WIN RI1 RI2 RO DBK KA;
      unfold B_HEAD; intros m1 cbs bp llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws
                            sl0 sl1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x28 x29 x30 x31 ENm FRLm BPXm BDm GCB NEC.
    { exfalso. unfold get_cblock_size, ZD_blockHeaderSize in GCB. replace (rem <? 3) with true in GCB by (symmetry; apply Z.ltb_lt; lia). discriminate GCB. }
    pose proof FOK as (ROFF & RSZ & RT & RMT & ACC & R9 & EHSZ & RH & NSK & GFH).
    pose proof (get_cblock_size_ok src OK ipb rem cbs bp GCB) as (R3 & EBP & RBT & RBL & RBO & RC). specialize (RC NEC).
    destruct RC as (NRSV & RCBS & _ & _). change (2^21) with 2097152 in *. unfold ZD_blockHeaderSize in *.
    pose proof (frame_header_size_range src off ZD_FRAMEHEADERSIZE_PREFIX ltac:(unfold ZD_FRAMEHEADERSIZE_PREFIX; lia)) as RHS.
    rewrite <- EHSZ in RHS. unfold ZD_FRAMEHEADERSIZE_MIN, ZD_FRAMEHEADERSIZE_MAX in RHS.
    pose proof FRLm as FRLm'. unfold RZ_dmf_a.frl_cells in FRLm'.
    pose proof BPXm as BPXm'. unfold bp_cells in BPXm'.
    pose proof ENm as (GOTm & SBm & DSKm & (csb & BPCm & BSZm) & (jt & FRHm) & STm & MUm & WMm & MIm).
    pose proof DSKm as (DST0 & _ & _).
    pose proof (bytes_at_bound _ _ _ _ SBm) as DB. rewrite length_map in DB.
    pose proof (B_DCTX_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BDm) as DAm.
    pose proof DNULL as DN1. pose proof DNN as DN2. unfold zimp in DN1, DN2.
    zs. replace (SRC + ipb + 3) with (SRC + (ipb + 3)) by lia.
    zs. zs. zs. fck. zs. zs. if_cases KFIT; zify_cond KFIT.
    - (* [comment removed for export] *)
      eapply (L_errx2 m1 off sz tot mt1); try eassumption; lia.
    - assert (BOK : BLK_OK off sz tot hsz PFX ipb rem o cbs bp).
      { split; [exact WIN|]. split; [exact RI1|]. split; [exact RI2|]. split; [exact RO|]. split; [exact GCB|]. split; [exact NEC|]. split; [lia| exact DBK]. }
      assert (KB : forall v, block_result (CAP - tot - o) cbs bp v -> 0 <= v -> bp_last bp = 0 ->
                   B_HEAD off sz tot mt1 h PFX (ipb + 3 + cbs) (rem - 3 - cbs) (o + v)).
      { intros v BR RV KL.
        assert (RV2 : v <= CAP - tot - o).
        { unfold block_result in BR. destruct (bp_type bp =? bt_raw); [lia|]. destruct (bp_type bp =? bt_rle); lia. }
        apply (IH off sz tot mt1 hsz h PFX); try assumption; try lia.
        intros ip' rem' o' DB'. apply DBK.
        eapply (DB_more src (CAP - tot) ipb rem o cbs bp v); [exact GCB | exact NEC | unfold ZD_blockHeaderSize; lia | exact BR | exact KL |].
        unfold ZD_blockHeaderSize. exact DB'. }
      clear IH.
      assert (DISPATCH : forall mx rm (w : word), ENV mx -> FRLB mx mt1 sl0 (Z_to_bv 64 (rem + -3)) (Z_to_bv 64 (DST + tot + o)) ->
          rw_cells usegs mx (SP + -168) (bp_cells bp) -> B_DCTX mx h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws ->
          w = Z_to_bv 64 (DST + tot + o + rm) -> 0 <= rm <= CAP - tot - o ->
          evt usegs POST (STpc 0x1589c mx x1 x5 x6 x7 (Z_to_bv 64 (DST + CAP)) (Z_to_bv 64 (DST + tot)) w x11 x12 (Z_to_bv 64 (DST + tot + o))
                           x14 x15 x16 x17 x18 (Z_to_bv 64 (CAP - tot)) (Z_to_bv 64 DCTX) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + (ipb + 3)))
                           x23 x24 (Z_to_bv 64 (DCTX + 29928)) (Z_to_bv 64 rem) (Z_to_bv 64 (-72)) x28 x29 x30 x31)).
      { intros mx rm w ENx FRLx BPXx BDx -> RRM.
        pose proof BPXx as BPXx'. unfold bp_cells in BPXx'.
        zs. rewrite sx32w_small by lia. zs. if_cases K0; zify_cond K0.
        - eapply (L_raw mx off sz tot mt1 hsz h PFX ipb rem o cbs bp); try eassumption.
        - zs. zs. if_cases K2; zify_cond K2.
          + eapply (L_cmp mx off sz tot mt1 hsz h PFX ipb rem o cbs bp rm); try eassumption.
          + zs. zs. if_cases K1; zify_cond K1;
              first [ exfalso; unfold bt_reserved in NRSV; lia
                    | eapply (L_rle mx off sz tot mt1 hsz h PFX ipb rem o cbs bp rm); try eassumption ]. }
      assert (MU3 : munch [(SP + -272, SP + -168)] m1 m1) by apply munch_refl.
      assert (WM3 : wmono usegs m1 m1) by apply wmono_refl.
      pose proof MIm as MIm0.
      pose proof S_SR as S_SR_; pose proof S_GT as S_GT_; unfold zsep in S_SR_, S_GT_. zs. clear S_SR_ S_GT_.
      lazymatch type of MU3 with munch _ _ ?m2 =>
        assert (BD2 : B_DCTX m2 h PFX llt mlt oft huf pde expd pcs dsz bt stg le fe xs ws)
          by (eapply (B_DCTX_transport _ m1 m2); [exact BDm | exact MU3 | exact WM3 | eassumption | eassumption | dj_solve]);
        assert (EN2 : ENV m2)
          by (split; [exact GOTm|]; split; [exact SBm|]; split; [exact DSKm|]; split; [exists csb; split; [exact BPCm| exact BSZm]|];
              split; [exists jt; exact FRHm|]; split; [exact STm|]; split; [exact MUm|]; split; [exact WMm| eassumption])
      end.
      clear BDm ENm MU3 WM3.
      zs. zs. if_cases LA; zify_cond LA.
      + eapply (DISPATCH _ (CAP - tot - o)); try eassumption; try (f_equal; lia); lia.
      + zs. zs. if_cases LB; zify_cond LB.
        * eapply (DISPATCH _ (CAP - tot - o)); try eassumption; try (f_equal; lia); lia.
        * zs. fck. zs. zs. fck. zs.
          eapply (DISPATCH _ (SRC + (ipb + 3) - (DST + tot + o))); try eassumption; try (f_equal; lia); lia.
  Qed.
End DMFC.
(* [comment removed for export] *)
