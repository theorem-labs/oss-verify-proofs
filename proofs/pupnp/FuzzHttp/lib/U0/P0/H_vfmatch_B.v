(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
Ltac vlit := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let p := eval vm_compute in pc in change pc with p end.
Ltac vwalk off := let p := eval vm_compute in (vfmatch_entry + off)%Z in uwalk_ub_to p.
Ltac xor_ok :=
  lazymatch goal with |- context [Z.lxor (Z.b2z (0 <? ?X)) (Z.b2z (?Y <? 1))] =>
    replace (Z.lxor (Z.b2z (0 <? X)) (Z.b2z (Y <? 1))) with 1;
    [| destruct (Z.ltb_spec 0 X); destruct (Z.ltb_spec Y 1); try lia; reflexivity ]
  end.

Section VF2.
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

  #[using="VOK"] Lemma L_loop : forall (k : nat) (fp G cs cur curi P : Z) (pw2 : word) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    (len - curi < Z.of_nat k)%Z -> (cur0 <= cur <= curi)%Z -> (curi <= len)%Z ->
    linv [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m0 m curi w8 cs ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 pw2] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z
                 (fun m' r cur' => exists pa pb, rw_cells rsegs m' P [C8 pa; C8 pb] /\ pa = wz (A + cur)
                     /\ (r = PARSE_OK -> exists l, pb = wz l /\ 0 <= l /\ cur' = cur + l /\ cur' < len
                           /\ exists b, nth_error bs (Z.to_nat cur') = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))%Z (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz (G + 8)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (fp + 2)) (wz cur) (wz P) (wz 37) (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz (vfmatch_entry + 1056)) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC HL LI PCH PL FP GR CS; [lia|].
    open_linv LI.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    vlit. vwalk 1068. step.
    sgtcall (q + -120) (q + -136) curi. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - rewrite ?(sx32_lit ty) by lia. vwalk 1056.
      if_cases K1; zify_cond K1.
      + vwalk 1056.
        eapply (IH fp G cs cur (curi + tlz)%Z P); try lia; [close_linv| exact PCH].
      + vwalk 144.
        replace (curi + tlz - tlz)%Z with curi in * by lia.
        dfinish rr curi. do 2 eexists; split; [eassumption|]. split; [reflexivity|]. intros _. exists (curi - cur)%Z.
        split; [f_equal; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. apply CRB. unfold TT_CRLF. lia.
    - vwalk 144. dfinish rr curi. do 2 eexists; split; [exact PCH|]. split; [reflexivity|]. intros; exfalso; lia.
  Qed.

  #[using="VOK"] Lemma dir_L : forall (fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 76 ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C8 pw1; C8 pw2] -> (q + 64 <= P /\ P + 16 <= MB)%Z -> (P mod 8 = 0)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z
                 (fun m' r cur' => exists pa pb, rw_cells rsegs m' P [C8 pa; C8 pb] /\ pa = wz (A + cur)
                     /\ (r = PARSE_OK -> exists l, pb = wz l /\ 0 <= l /\ cur' = cur + l /\ cur' < len
                           /\ exists b, nth_error bs (Z.to_nat cur') = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))%Z (fun _ => False) m)
        (headst gp tp F fc fp 37 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2 GC PCH PL P8.
    eapply (pct_dispatch q lo S MB A len cap cur0 bs VOK _ fp 76); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    vlit. vwalk 1056. xor_ok. vwalk 1056.
    replace (cur + A)%Z with (A + cur)%Z in * by lia.
    eapply (L_loop (Datatypes.S (Z.to_nat (len - cur))) fp G cs cur cur P); try lia; [close_linv| eassumption].
  Qed.

  Definition XS (cur P : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb, rw_cells rsegs m' P [C8 pa; C8 pb]
       /\ (r = PARSE_OK -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len))%Z.

  #[using="VOK"] Lemma S_exit_err : forall (fp G cs cur curi P r : Z) (pa pb : word) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    (cur0 <= cur <= len)%Z -> (0 <= curi <= len)%Z -> (r = 1 \/ r = 3)%Z ->
    linv [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m0 m curi w8 cs ->
    rw_cells rsegs m P [C8 pa; C8 pb] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z (XS cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz (G + 8)) (wz r) x11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz 83) (wz P) (wz cur)
               (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 0x14674) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    intros until m; intros HC HCI HR LI PCH PL FP GR CS. open_linv LI.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. if_cases K0; zify_cond K0.
    -   zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
      sstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
      unfold XS; dfinish r cur. do 2 eexists; split; [exact PCH|]. intros; exfalso; lia.
    - zstep. if_cases K1; zify_cond K1. 2:{ exfalso; lia. }
      sstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso; lia. }
      unfold XS; dfinish r cur. do 2 eexists; split; [exact PCH|]. intros; exfalso; lia.
  Qed.

  #[using="VOK"] Lemma S_exit_ok : forall (fp G cs cur l tl2 P : Z) (tbw : word) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    (cur0 <= cur)%Z -> (0 <= l)%Z -> (1 <= tl2)%Z -> (cur + l + tl2 <= len)%Z ->
    linv [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m0 m (cur + l + tl2) w8 cs ->
    F88 m tbw (wz tl2) ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 (wz l)] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z (XS cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz (G + 8)) (wz 4) x11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz 83) (wz P) (wz cur)
               (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 0x14674) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    intros until m; intros HC HL0 TL2 HB LI F88T PCH PL FP GR CS. open_linv LI.
    unfold H_vfmatch_A.F88 in F88T. clear FR88.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
    zstep. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. zstep. zstep. sstep. zstep.
    replace (cur + l + tl2 - tl2)%Z with (cur + l)%Z in * by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep.
    match goal with |- context [Z_to_bv 64 (Z.b2z ?bb + 4)] => destruct bb eqn:EB end.
    - unfold XS. dfinish 5 (cur + l)%Z. do 2 eexists; split; [exact PCH|]. intros; exfalso; lia.
    - unfold XS. dfinish 4 (cur + l)%Z. do 2 eexists; split; [exact PCH|]. intros _. exists l. repeat split; try reflexivity; try lia.
      all: cond_norm EB; lia.
  Qed.

  Ltac sgn_mod K := change 18446744073709551616%Z with (2^64)%Z in K; rewrite ?mod64_small_signed in K by lia;
    repeat match type of K with context [if (?x <? 0)%Z then _ else _] => destruct (Z.ltb_spec0 x 0) end.

  #[using="VOK"] Lemma S_loop : forall (k : nat) (fp G cs cur l tlz P : Z) (tbw : word) gp tp (F : bvmap 5 word) fc (w8 : word) m0
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m,
    (len - (cur + l + tlz) < Z.of_nat k)%Z -> (cur0 <= cur)%Z -> (0 <= l)%Z -> (1 <= tlz)%Z -> (cur + l + tlz <= len)%Z ->
    linv [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m0 m (cur + l + tlz) w8 cs ->
    F88 m tbw (wz tlz) ->
    rw_cells rsegs m P [C8 (wz (A + cur)); C8 (wz l)] -> (q + 64 <= P /\ P + 16 <= MB)%Z ->
    (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z (XS cur P) (fun _ => False) m0)
      (MS (mkR x1 (wz qq) gp tp x5 x6 x7 (wz S) (wz (G + 8)) x10 x11 x12 x13 x14 x15 x16 x17 (wz (fp + 2)) (wz 83) (wz P) (wz cur)
               (wz 1) (wz 4) (wz 9) (wz 32) (wz 2) (wz cur0) x28 x29 x30 x31)
          F (wz 0x14640) fc None m (seg_rom rsegs)).
  Proof.
    vok VOK.
    induction k as [|k IH]; intros until m; intros HK HC HL0 TL1 HB LI F88T PCH PL FP GR CS; [lia|].
    open_linv LI. unfold H_vfmatch_A.F88 in F88T. clear FR88.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    pose proof (rw_cells_bound rsegs _ _ _ SC) as SB. cbn [cells_size csize Nat.add] in SB.
    zstep. zstep. zstep. sstep. zstep. zstep. zstep. zstep.
    replace (l + tlz)%Z with (l + tlz)%Z in * by lia.
    sgtcall (q + -120) (q + -136) (cur + l + tlz)%Z. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz2 & ty & HR & -> & -> & -> & TL2 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. rewrite (sx32_lit ty) by lia. zstep. rewrite swrap32_id by lia. zstep. zstep. if_cases K1; zify_cond K1.
      +   sgn_mod K1; try lia.
        all: replace (cur + l + tlz + tlz2)%Z with (cur + (l + tlz) + tlz2)%Z in * by lia.
        all: replace (tlz + l)%Z with (l + tlz)%Z in PCH by lia.
        all: eapply (IH fp G cs cur (l + tlz)%Z tlz2 P); try lia; [close_linv| exact TC| exact PCH].
      + sgn_mod K1; try lia. subst rr.
        replace (cur + l + tlz + tlz2)%Z with (cur + (l + tlz) + tlz2)%Z in * by lia.
        replace (tlz + l)%Z with (l + tlz)%Z in PCH by lia.
        eapply (S_exit_ok fp G cs cur (l + tlz)%Z tlz2 P); try lia; [close_linv| exact TC| exact PCH].
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      eapply (S_exit_err fp G cs cur (cur + l + tlz)%Z P rr); try lia; [close_linv| ].
      exact PCH.
  Qed.

  #[using="VOK"] Lemma dir_S : forall (fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) gp tp (F : bvmap 5 word) fc
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (w8 ty36 tb tl e72 ty84 tb2 tl2 : word) m,
    SCc m cur -> MBc m -> BUFc m -> (cur0 <= cur <= len)%Z ->
    F0 m w8 cs -> F36 m ty36 -> F40 m tb tl -> F56 m -> F72 m e72 -> F76 m -> F84 m ty84 -> F88 m tb2 tl2 ->
    stk rsegs m lo qq -> mem_inv rsegs m -> (0 <= fp /\ fp + 2 < 2^63)%Z -> (q + 16 <= G /\ G + 8 <= q + 64)%Z -> (0 <= cs <= 1)%Z ->
    ov_read_bytes rsegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 83 ->
    rw_cells rsegs m G [C8 (wz P)] -> rw_cells rsegs m P [C8 pw1; C8 pw2] -> (q + 64 <= P /\ P + 16 <= MB)%Z -> (P mod 8 = 0)%Z ->
    evt rsegs (dpost gp tp F fc (fp + 2) (G + 8) cs [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z (XS cur P) (fun _ => False) m)
        (headst gp tp F fc fp 37 G x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m).
  Proof.
    vok VOK.
    intros until m. intros SC MBC BUF CUR FR0 FR36 FR40 FR56 FR72 FR76 FR84 FR88 ST MI FP GR CS RD Hb2 GC PCH PL P8.
    eapply (pct_dispatch q lo S MB A len cap cur0 bs VOK _ fp 83); [exact MI| reflexivity| lia| exact RD| exact Hb2|]. cbn [vjt_off Z.eqb Pos.eqb Z.add]. unf.
    pose proof (munch_refl [(q - 304, q - 104); (S + 8, S + 16); (P, P + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    vlit. vwalk 1296. xor_ok. vwalk 1296.
    replace (cur + A)%Z with (A + cur)%Z in * by lia.
    zstep.
    sgtcall (q + -120) (q + -136) cur. name_r.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & _ & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - zstep. if_cases K0; zify_cond K0. { exfalso; lia. }
      zstep. rewrite (sx32_lit ty) by lia. zstep. rewrite swrap32_id by lia. zstep. zstep. if_cases K1; zify_cond K1.
      +   sgn_mod K1; try lia. subst rr.
        replace (cur + tlz)%Z with (cur + 0 + tlz)%Z in SC by lia.
        eapply (S_exit_ok fp G cs cur 0 tlz P); try lia; [close_linv| exact TC| exact PCH].
      + sgn_mod K1; try lia.
        all: replace (cur + tlz)%Z with (cur + 0 + tlz)%Z in SC by lia.
        all: eapply (S_loop (Datatypes.S (Z.to_nat (len - cur))) fp G cs cur 0 tlz P); try lia; [close_linv| exact TC| exact PCH].
    - zstep. if_cases K0; zify_cond K0. 2:{ exfalso; lia. }
      eapply (S_exit_err fp G cs cur cur P rr); try lia; [close_linv| exact PCH].
  Qed.

End VF2.
