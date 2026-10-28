(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac sstep := step; fix_lit_store.

Ltac vfr_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.
Ltac vfr_xor H :=
  match goal with |- context [Z.lxor (Z.b2z ?c1) (Z.b2z ?c2)] =>
    let E := fresh "E" in
    assert (E : Z.lxor (Z.b2z c1) (Z.b2z c2) = 1) by (destruct H as [?|[? ?]]; vfr_b2z; reflexivity);
    rewrite E; clear E end.

Section VFR.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.


  Definition XR (cur P : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb, rw_cells rsegs m' P [C8 pa; C8 pb]
       /\ (r = PARSE_OK -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 0 <= l /\ cur + l <= len /\ cur <= cur' /\ cur + l <= cur' + 2))%Z.
  Notation WP P := [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z.

  #[using="VOK"] Lemma R_trim : forall (k : nat) (fp G cs cur pos j P : Z) gp tp (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x13 x15 x16 x17 x20 x28 x29 x30 x31 m,
    (j < Z.of_nat k)%Z -> (cur0 <= cur)%Z -> (0 <= j)%Z -> (cur + j < len)%Z -> (cur <= pos <= len)%Z -> (cur + j + 1 <= pos + 2)%Z ->
    linv (WP P) m0 m pos (wz cur0) cs ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 (wz (j + 1))] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) (wz 4) (wz (A + cur)) (wz j) x13 (wz MASK) x15 x16 x17 (wz (fp + 2)) (wz P) x20
               (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 0x1486c) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC HJ HB HP HJP LI PCH PL FP GR CS; [lia|].
    open_linv LI.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bs q lo S MB A len cap cur0 bs VOK (cur + j) ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs _ A bs (cur + j) b (Z_to_bv 64 (A + cur + j)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.

    assert (EXIT : forall (l' : Z) y11 y12 y13 m', (0 <= l' <= j + 1)%Z ->
      linv (WP P) m0 m' pos (wz cur0) cs -> rw_cells rsegs m' P [C8 (wz (A + cur)); C8 (wz l')] ->
      evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m0)
        (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) (wz 4) y11 y12 y13 (wz MASK) x15 x16 x17 (wz (fp + 2)) (wz P) x20
                 (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
            F (wz 0x14834) fc None m' (seg_rom rsegs))).
    { intros until m'. intros HL' LI' PCH'. clear SC MBC BUF FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI MU WM RD PCH. open_linv LI'.
      zstep. zstep. unfold XR. dfinish 4 pos. do 2 eexists; split; [exact PCH'|]. intros _. exists l'. repeat split; try reflexivity; lia. }
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    -   apply (EXIT (j + 1)%Z); [lia| close_linv| exact PCH].
    - zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + apply (EXIT (j + 1)%Z); [lia| close_linv| exact PCH].
      + sstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
        *   replace (j + -1)%Z with (j - 1)%Z by lia.
          eapply (IH fp G cs cur pos (j - 1)%Z P); try lia; [close_linv|]. replace (j - 1 + 1)%Z with j by lia. exact PCH.
        * zstep. apply (EXIT j); [lia| close_linv| exact PCH].
  Qed.

  #[using="VOK"] Lemma R_done : forall (fp G cs cur ci pos l P : Z) gp tp (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x27 x28 x29 x30 x31 m,
    (cur0 <= cur)%Z -> (0 <= l)%Z -> (cur + l <= len)%Z -> (cur <= pos <= len)%Z -> (0 <= ci <= len)%Z -> (cur + l <= pos + 2)%Z ->
    linv (WP P) m0 m ci (wz cur0) cs ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 (wz l)] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) x10 x11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz P) x20 (wz pos)
               (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) x27 x28 x29 x30 x31)
          F (wz 0x1483c) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    intros until m; intros HC HL HB HP HCI HLP LI PCH PL FP GR CS. open_linv LI.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    sstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    -   zstep. zstep. zstep. zstep. unfold XR. dfinish 4 pos.
      do 2 eexists; split; [exact PCH|]. intros _. exists l. repeat split; try reflexivity; lia.
    - zstep. zstep. zstep. step. ubr. zstep. step. ubr. zstep. zstep. replace (l + -1)%Z with (l - 1)%Z by lia.
      eapply (R_trim (Datatypes.S (Z.to_nat l)) fp G cs cur pos (l - 1)%Z P); try lia; [close_linv|].
      replace (l - 1 + 1)%Z with l by lia. exact PCH.
  Qed.

  #[using="VOK"] Lemma R_loop : forall (k : nat) (fp G cs cur ci tlz ty saw pos P : Z) gp tp (F : bvmap 5 word) fc m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    (len - (ci + tlz) < Z.of_nat k)%Z -> (cur0 <= cur <= ci)%Z -> (1 <= tlz)%Z -> (ci + tlz <= len)%Z -> (0 <= ty <= 5)%Z ->
    (saw = 0 \/ (saw = 1 /\ cur <= pos <= ci /\ ci <= pos + 2))%Z -> (ty = 2 -> tlz <= 2)%Z ->
    linv (WP P) m0 m (ci + tlz) (wz cur0) cs -> F88 m (wz (A + ci)) (wz tlz) -> F72 m (wz ty) ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 (wz (ci - cur))] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) x10 x11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz P) (wz cur) (wz pos)
               (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz saw) x28 x29 x30 x31)
          F (wz 0x144b8) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC TL1 HB TY5 SAW CRLX LI F88T F72T PCH PL FP GR CS; [lia|].
    open_linv LI. unfold H_vfmatch_A.F88 in F88T. unfold H_vfmatch_A.F72 in F72T. clear FR88 FR72.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.

    assert (CONT : forall (saw' pos' : Z) y11 m', (saw' = 0 \/ (saw' = 1 /\ cur <= pos' <= ci + tlz /\ ci + tlz <= pos' + 2))%Z ->
      linv (WP P) m0 m' (ci + tlz) (wz cur0) cs -> rw_cells rsegs m' P [C8 (wz (A + cur)); C8 (wz (ci - cur))] ->
      evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m0)
        (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz G) (wz tlz) y11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz P) (wz cur) (wz pos')
                 (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz saw') x28 x29 x30 x31)
            F (wz 0x14498) fc None m' (seg_rom rsegs))).
    { intros until m'. intros SAW' LI' PCH'. clear SC MBC BUF FR0 FR36 FR40 FR56 FR76 FR84 ST MI MU WM F88T F72T PCH. open_linv LI'.
      pose proof (bytes_at_bound _ _ _ _ BUF) as BB'.
      zstep. zstep. sstep. zstep. zstep. zstep. zstep.
      replace (ci - cur + tlz)%Z with (ci + tlz - cur)%Z in * by lia.
      sgtcall (q + -120) (q + -136) (ci + tlz)%Z. name_r.
      unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
      destruct RES as [(tlz2 & ty2 & HR & -> & -> & -> & TL2 & -> & _ & TY52 & STRICT2 & CRB2 & CRL2)|(HR & -> & ->)].
      - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
        eapply (IH fp G cs cur (ci + tlz)%Z tlz2 ty2 saw' pos' P); try lia. 1:{ unfold TT_CRLF in CRL2. exact CRL2. } all: first [close_linv| exact TC| exact TYC| exact PCH'].
      - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
        zstep. zstep. sstep. zstep. zstep. unfold XR. dfinish rr cur.
        do 2 eexists; split; [exact PCH'|]. intros; exfalso; lia. }
    zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K1; zify_cond K1.
    -   zstep. zstep. if_cases K2; zify_cond K2.
      +   zstep. apply (CONT 0 pos); [lia| close_linv| exact PCH].
      +   zstep. zstep. zstep. zstep.
        replace (ci + tlz - tlz)%Z with ci by lia. apply (CONT 1 ci); [lia| close_linv| exact PCH].
    -   zstep. if_cases K2; zify_cond K2.
      + eapply (R_done fp G cs cur (ci + tlz)%Z pos (ci - cur)%Z P); try lia; [close_linv|].
        exact PCH.
      + zstep. zstep. zstep. apply (CONT 0 pos); [lia| close_linv| exact PCH].
  Qed.

  #[using="VOK"] Lemma dir_R : forall (fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 82 ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C8 pw1; C8 pw2] -> (q + 64 <= P /\ P + 16 <= MB)%Z -> (P mod 8 = 0)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs (WP P) (XR cur P) (fun _ => False) m)
        (headst gp tp F fc fp 37 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2 GC PCH PL P8.
    eapply (pct_dispatch q lo S MB A len cap cur0 bs VOK _ fp 82); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl (WP P) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. ub_null. ub_align.
    zstep. zstep. zstep.
    try replace (Z_to_bv 64 (cur + A)) with (Z_to_bv 64 (A + cur)) by (f_equal; lia).
    step. ubr.
    zstep. zstep. zstep. vfr_xor ANZ. step. lit_branch.
    zstep. ub_null. ub_align.
    sstep. sstep.
    zstep. zstep. zstep. zstep.
    sgtcall (q + -120) (q + -136) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      sstep. zstep. zstep. zstep.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (cur - cur)) in PCH by (f_equal; lia).
      eapply (R_loop (Datatypes.S (Z.to_nat (len - cur))) fp G cs cur cur tlz ty 0 0 P); try lia. 1:{ unfold TT_CRLF in CRL. exact CRL. } all: first [close_linv| exact TC| exact TYC| exact PCH].
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      sstep. zstep. zstep. unfold XR. dfinish rr cur. do 2 eexists; split; [exact PCH|]. intros; exfalso; lia.
  Qed.
End VFR.
