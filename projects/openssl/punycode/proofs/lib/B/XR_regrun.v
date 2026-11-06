(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Arr Walk Image SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRehashModel AsanRegModel AsanRegStmt B_RegConsts.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow R_arrkit.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout RT_iface R_small R_cache_defs F_memset X_atexit X_gdefs X_unregi XR_rehash XR_kit XR_probe XR_iter XR_iterw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma d_okb_A : forall d, RGM.d_okb B_RGL d = true ->
  0x10000 <= RGM.d_beg d /\ RGM.d_beg d mod 8 = 0 /\ RGM.d_swr d mod 8 = 0 /\ 1 <= RGM.d_size d /\ RGM.rup8 (RGM.d_size d) <= RGM.d_swr d
  /\ RGM.d_swr d < 0x80000 /\ RGM.d_beg d + RGM.d_swr d <= 0xbfd000 /\ RGM.d_dyn d = 0
  /\ (RGM.d_odr d = RGM.ODR_NONE \/ 0xbd6a20 <= RGM.d_odr d < 0xbda496).
Proof.
  intros d H. unfold RGM.d_okb in H. cbn [B_RGL RGM.l_ilo RGM.l_ihi RGM.l_odr_lo RGM.l_odr_hi] in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with
  | X : (_ <=? _) = true |- _ => apply Z.leb_le in X
  | X : (_ <? _) = true |- _ => apply Z.ltb_lt in X
  | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X
  end.
  repeat split; try assumption; try lia.
Qed.

Lemma inds_cons_common : forall d r, RGM.is_ind d = false -> RGM.inds (d :: r) = RGM.inds r /\ RGM.nind (d :: r) = RGM.nind r.
Proof.
  intros d r H. unfold RGM.inds, RGM.nind.
  change (List.filter RGM.is_ind (d :: r)) with (if RGM.is_ind d then d :: List.filter RGM.is_ind r else List.filter RGM.is_ind r). rewrite H. split; reflexivity.
Qed.
Lemma inds_cons_ind : forall d r, RGM.is_ind d = true -> RGM.inds (d :: r) = RGM.d_odr d :: RGM.inds r /\ RGM.nind (d :: r) = 1 + RGM.nind r.
Proof.
  intros d r H. unfold RGM.inds, RGM.nind.
  change (List.filter RGM.is_ind (d :: r)) with (if RGM.is_ind d then d :: List.filter RGM.is_ind r else List.filter RGM.is_ind r). rewrite H.
  cbn [map length]. split; [reflexivity| lia].
Qed.
Lemma nind_nonneg : forall r, 0 <= RGM.nind r.
Proof. intros r. unfold RGM.nind. lia. Qed.

(* [comment removed for export] *)
Definition munchW (W : list ivl) (m0 m : mem) : Prop := munch W m0 m.

Lemma Forall_upd : forall (P : Z -> Prop) ks i v, Forall P ks -> P v -> Forall P (RGM.upd ks i v).
Proof.
  intros P ks. induction ks as [|k r IH]; intros i v H Hv; [constructor|]. inversion H; subst.
  destruct i as [|i]; cbn [RGM.upd]; constructor; auto.
Qed.

(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.
Ltac keep_all m :=
  repeat match goal with
  | H : ?T |- _ => lazymatch T with keep _ => fail | context [m] => change T with (keep T) in H end
  end.
Ltac drop_kept := repeat match goal with H : keep _ |- _ => clear H end.

Section Run.
Variables (fp n : Z) (gp tp s3 s10 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (B N : Z) (hm : bool) (W : list ivl) (m0 : mem) (SLO SHI C0 CEND lend : Z).
Local Notation st_entry := (XR_iter.st_entry fp gp tp s3 s10 F fc) (only parsing).
Hypothesis Hn : TABA + 64 * n <= 0x6a03c0.
Hypothesis SPlo : 0x80177a00 <= fp - 0x10f0 - 32.
Hypothesis FPhi : fp < 2 ^ 47.
Hypothesis HC0 : 0 < C0.
Hypothesis HCE : CEND <= lend.
Hypothesis HLE : lend < 2 ^ 47.
Hypothesis AI : CEND <= 0x10000 \/ 0xbfd000 <= C0.
Hypothesis ASH : CEND <= SHW_LO \/ SHW_HI <= C0.
Hypothesis AFR : CEND <= fp - 0x10f0 - 32 \/ fp <= C0.
Hypothesis HSL : 0x7fffa000 <= SLO /\ SHI <= 0x80177a00.
Hypothesis HMAP : hm = true -> 8 <= N <= 2 ^ 20 /\ 0 < B /\ B + 32 * N <= 2 ^ 47 /\ (B + 32 * N <= 0x10000 \/ 0xbfd000 <= B)
                               /\ (B + 32 * N <= SHW_LO \/ SHW_HI <= B) /\ (B + 32 * N <= C0 \/ CEND <= B)
                               /\ (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B).
Hypothesis HW_fix : forall x, outside W x ->
  outside [(fp + -4264, fp + -4256); (fp - 0x10f0 - 32, fp - 0x10f0); (SLO, SHI); (0x6a12f8, 0x6a1308); (LLA + 8, LLA + 16); (C0, CEND)] x.
Hypothesis HW_map : hm = true -> forall x, outside W x -> outside [(MAPA + 8, MAPA + 12); (B, B + 32 * N)] x.

(* [comment removed for export] *)
Definition ro_area (x : Z) : Prop :=
  TABA <= x < 0x6a03c0 \/ 0x5e4190 <= x < 0x5e4198 \/ 0x5e41d0 <= x < 0x5e41d8 \/ 0x6a1290 <= x < 0x6a1294 \/ 0x6a12cd <= x < 0x6a12ce
  \/ 0x6a12dc <= x < 0x6a12e0 \/ 0x6a1328 <= x < 0x6a1330 \/ 0x6a32dc <= x < 0x6a32dd \/ 0x6a3a78 <= x < 0x6a3a80 \/ 0x6a4758 <= x < 0x6a4759
  \/ fp + -4304 <= x < fp + -4264.
Hypothesis HW_ro : forall x, ro_area x -> outside W x.

Lemma munch_ro : forall m A nn, munchW W m0 m -> (forall x, A <= x < A + nn -> ro_area x) -> munch [(0, A); (A + nn, 2 ^ 64)] m0 m.
Proof.
  intros m A nn MU HA x Hx. apply MU. apply HW_ro. apply HA. cbn [outside] in Hx.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma ro_keep : forall m A cs, munchW W m0 m -> ro_cells bsegs m0 A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> ro_area x) -> ro_cells bsegs m A cs.
Proof.
  intros m A cs MU H HA. apply (ro_cells_transport bsegs _ m0 m A cs H (munch_ro m A _ MU HA)).
  cbn [disjoint_from]. lia.
Qed.

Lemma rw_keep : forall m A cs, munchW W m0 m -> wmono bsegs m0 m -> rw_cells bsegs m0 A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> ro_area x) -> rw_cells bsegs m A cs.
Proof.
  intros m A cs MU WM H HA. apply (rw_cells_transport bsegs _ m0 m A cs H (munch_ro m A _ MU HA) WM).
  cbn [disjoint_from]. lia.
Qed.

Ltac ro_side := cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold ro_area; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  first [ lazymatch goal with G : TABA <= _ /\ _ + 64 <= 0x6a03c0 |- _ => clear -Hx G end | clear -Hx ]; lia.


Definition first_after (ds : list RGM.desc) (first : Z) : Z := match ds with [] => first | _ :: _ => CEND - 16 end.

(* [comment removed for export] *)
Hypothesis AIN0 : rw_cells bsegs m0 0x6a4758 [C1 (Z_to_bv 8 1)].
Hypothesis RG0 : ro_cells bsegs m0 0x6a1290 [C4 (Z_to_bv 64 1)].
Hypothesis DO0 : ro_cells bsegs m0 0x6a12dc [C4 (Z_to_bv 64 2)].
Hypothesis PP0 : ro_cells bsegs m0 0x6a12cd [C1 (Z_to_bv 8 1)].
Hypothesis SHC0 : ro_cells bsegs m0 0x6a3a78 [C8 (Z_to_bv 64 0x7fff8000)].
Hypothesis CP0 : ro_cells bsegs m0 0x6a32dc [C1 (Z_to_bv 8 1)].
Hypothesis MSC0 : ro_cells bsegs m0 0x5e4190 [C8 (Z_to_bv 64 0x563738)].
Hypothesis AL0 : ro_cells bsegs m0 0x5e41d0 [C8 (Z_to_bv 64 8)].
Hypothesis NS0 : ro_cells bsegs m0 (fp + -4272) [C8 (Z_to_bv 64 n)].
Hypothesis MP0 : ro_cells bsegs m0 (fp + -4304) [C8 (Z_to_bv 64 0x5e4190)].
Hypothesis MPC0 : hm = true -> rw_cells bsegs m0 0x6a1328 [C8 (Z_to_bv 64 MAPA)].

Lemma reg_loop : forall (ds : list RGM.desc) (i : Z) (ks : list Z) (ne : Z) (ks' : list Z) (ne' : Z) (cur lsize first : Z) (nws : list word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 : word) (m : mem),
  RGM.run B_RGL N ds ks ne = Some (ks', ne') ->
  0 <= i -> i + Z.of_nat (length ds) < n ->
  (forall j, 0 <= j < Z.of_nat (length ds) -> RGS.desc_at bsegs m0 (TABA + 64 * (i + j)) (nth (Z.to_nat j) ds RGS.dflt)) ->
  List.NoDup (RGM.inds ds) ->
  (forall o, In o (RGM.inds ds) -> rw_cells bsegs m o [C1 (Z_to_bv 8 0)]) ->
  (forall o, In o (RGM.inds ds) -> forall x, outside W x -> ~ (o <= x < o + 1)) ->
  (forall o, In o (RGM.inds ds) -> 0xbd6a20 <= o < 0xbda496) ->
  Forall (fun d => SLO <= RGM.sh_lo1 B_RGL d /\ RGM.sh_hi1 B_RGL d <= SHI) ds ->
  (0 < RGM.nind ds -> hm = true) ->
  C0 <= cur -> cur + 16 * (Z.of_nat (length ds) + RGM.nind ds) = CEND ->
  munchW W m0 m -> wmono bsegs m0 m ->
  stk bsegs m (fp + -4264) (fp + -4256) ->
  stk bsegs m (fp - 0x10f0 - 32) (fp - 0x10f0) ->
  stk bsegs m SHW_LO SHW_HI ->
  rw_cells bsegs m LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)] ->
  stk bsegs m cur CEND ->
  rw_cells bsegs m 0x6a12f8 [C8 (Z_to_bv 64 lsize); C8 (Z_to_bv 64 first)] -> 1 <= lsize -> lsize + Z.of_nat (length ds) < 2 ^ 63 ->
  (hm = true -> rw_cells bsegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
                /\ u64arr bsegs m B nws /\ keys_rep (Z.to_nat N) nws ks /\ 0 <= ne /\ Forall (fun k => 0 <= k < 2 ^ 64) ks) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' s7' t3' t4' t5' t6' : word) (nws' : list word) (m' : mem),
      ms' = st_entry (i + Z.of_nat (length ds)) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s6' s7' t3' t4' t5' t6' 0x1a4458 m'
      /\ munchW W m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' LLA [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 CEND)]
      /\ rw_cells bsegs m' 0x6a12f8 [C8 (Z_to_bv 64 (lsize + Z.of_nat (length ds))); C8 (Z_to_bv 64 (first_after ds first))]
      /\ (hm = true -> rw_cells bsegs m' MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne'); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
                       /\ u64arr bsegs m' B nws' /\ keys_rep (Z.to_nat N) nws' ks'))
    (st_entry i ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 0x1a4458 m).
Proof.
  induction ds as [|d r IH]; intros i ks ne ks' ne' cur lsize first nws ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 t3 t4 t5 t6 m
    RUN Hi Hin HD ND INDS HWI HOW HSH HHM HCUR0 HCUR MU0 WM0 KSS FRS SCW LLC AST HDR LS1 LS2 HM MI.
  - (* [comment removed for export] *)
    cbn [RGM.run] in RUN. injection RUN as <- <-.
    change (RGM.nind []) with 0 in HCUR. cbn [length Z.of_nat] in *. replace CEND with cur by lia.
    apply evt_done. do 19 eexists. exists nws. eexists. split; [rewrite Z.add_0_r; reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact LLC|].
    split; [rewrite Z.add_0_r; exact HDR|].
    intros E. destruct (HM E) as (M2 & M3 & M4 & _). auto.
  - (* [comment removed for export] *)
    cbn [RGM.run] in RUN.
    destruct (RGM.d_okb B_RGL d) eqn:OK; cbn [negb] in RUN; [| discriminate].
    destruct (d_okb_A d OK) as (B0 & B8 & S8 & Z1 & RU & SW & BT & DY & OD).
    destruct d as [beg size swr dyn odr]. cbn [RGM.d_beg RGM.d_size RGM.d_swr RGM.d_dyn RGM.d_odr] in *. subst dyn.
    set (g := TABA + 64 * i).
    assert (HLEN : Z.of_nat (length (RGM.D beg size swr 0 odr :: r)) = 1 + Z.of_nat (length r)) by (cbn [length]; lia).
    rewrite HLEN in *.
    pose proof (HD 0 ltac:(lia)) as (REC0 & RDYN0 & RODR0).
    cbn [Z.to_nat nth RGM.d_beg RGM.d_size RGM.d_swr RGM.d_dyn RGM.d_odr] in REC0, RDYN0, RODR0.
    replace (TABA + 64 * (i + 0)) with g in REC0, RDYN0, RODR0 by (unfold g; lia).
    assert (G0 : TABA <= g /\ g + 64 <= 0x6a03c0) by (unfold g; clear -Hi Hin Hn; lia).
    inversion HSH as [|d0 r0 [HS1 HS2] HSHr]; subst d0 r0.
    unfold RGM.sh_lo1, RGM.sh_hi1, RGM.shad in HS1, HS2. cbn [B_RGL RGM.l_shb RGM.d_beg RGM.d_swr] in HS1, HS2.
    assert (HDr : forall j, 0 <= j < Z.of_nat (length r) -> RGS.desc_at bsegs m0 (TABA + 64 * (i + 1 + j)) (nth (Z.to_nat j) r RGS.dflt)).
    { intros j Hj. pose proof (HD (1 + j) ltac:(lia)) as X. replace (Z.to_nat (1 + j)) with (S (Z.to_nat j)) in X by lia. cbn [nth] in X.
      replace (TABA + 64 * (i + (1 + j))) with (TABA + 64 * (i + 1 + j)) in X by lia. exact X. }
    pose proof (nind_nonneg r) as NN.
    assert (SHL : 0x7fffa000 <= 0x7fff8000 + beg / 8) by (clear -B0; Z.div_mod_to_equations; lia).
    assert (SHH : 0x7fff8000 + (beg + swr) / 8 <= 0x80177a00) by (clear -BT; Z.div_mod_to_equations; lia).
    assert (C01 : 0 < cur) by (clear -HC0 HCUR0; lia).
    pose proof (ro_keep m g _ MU0 REC0 ltac:(ro_side)) as REC. pose proof (ro_keep m (g + 40) _ MU0 RDYN0 ltac:(ro_side)) as RDYN.
    pose proof (ro_keep m (g + 56) _ MU0 RODR0 ltac:(ro_side)) as RODR.
    pose proof (rw_keep m _ _ MU0 WM0 AIN0 ltac:(ro_side)) as AIN. pose proof (ro_keep m _ _ MU0 RG0 ltac:(ro_side)) as RG.
    pose proof (ro_keep m _ _ MU0 DO0 ltac:(ro_side)) as DO. pose proof (ro_keep m _ _ MU0 PP0 ltac:(ro_side)) as PP.
    pose proof (ro_keep m _ _ MU0 SHC0 ltac:(ro_side)) as SHC. pose proof (ro_keep m _ _ MU0 CP0 ltac:(ro_side)) as CP.
    pose proof (ro_keep m _ _ MU0 MSC0 ltac:(ro_side)) as MSC. pose proof (ro_keep m _ _ MU0 AL0 ltac:(ro_side)) as AL.
    pose proof (ro_keep m _ _ MU0 NS0 ltac:(ro_side)) as NS. pose proof (ro_keep m _ _ MU0 MP0 ltac:(ro_side)) as MP.
    destruct (RGM.is_ind (RGM.D beg size swr 0 odr)) eqn:EI; cbn [negb] in RUN.
    + (* [comment removed for export] *)
      assert (EOD : 0xbd6a20 <= odr < 0xbda496).
      { destruct OD as [E|OW]; [| exact OW]. subst odr. unfold RGM.is_ind in EI. cbn [RGM.d_odr] in EI. rewrite Z.eqb_refl in EI. discriminate EI. }
      destruct (inds_cons_ind _ r EI) as [EIND ENI]. cbn [RGM.d_odr] in EIND. rewrite EIND in *. rewrite ENI in *.
      assert (EH : hm = true) by (apply HHM; clear -NN; lia).
      destruct (HM EH) as (M2 & M3 & M4 & M5 & M6). destruct (HMAP EH) as (HN & HB0 & HBT & HBI & HBS & HBC & HBF).
      destruct (RGM.no_grow N ne) eqn:NG; cbn [negb] in RUN; [| discriminate].
      destruct (RGM.probe_ins N ks odr (RGM.hash0 N odr) 1 (Z.to_nat N)) as [p|] eqn:PI; [| discriminate].
      assert (CR2 : cur + 32 <= CEND) by (clear -HCUR NN; lia).
      inversion ND as [|o1 l1 NI NDr]; subst o1 l1.
      pose proof (INDS odr (or_introl eq_refl)) as IND0.
      pose proof (MPC0 EH) as MPCm0.
      eapply evt_cut.
      { eapply (reg_iter_ind fp n gp tp s3 s10 F fc i g beg size swr odr B N ne p lend cur CEND lsize first ks nws);
        [exact Hi| clear -Hin; lia| exact Hn| reflexivity| exact REC| exact RDYN| exact RODR
        | exact EOD| exact B0| exact B8| exact S8| exact Z1| exact RU| exact SW| exact BT
        | exact PI| exact NG| exact HN| exact M5| exact M6
        | exact (rw_keep m _ _ MU0 WM0 MPCm0 ltac:(ro_side))| exact M2| exact M3| exact M4
        | exact HB0| exact HBT| exact HBI| exact HBS| clear -HBC HCUR0; lia| exact HBF| exact IND0
        | exact AIN| exact RG| exact DO| exact PP| exact SHC| exact CP| exact MSC| exact AL| exact NS| exact MP
        | exact KSS| exact FRS| exact SPlo| exact FPhi| exact SCW| exact LLC| exact C01| exact CR2| exact HCE| exact HLE| exact AST
        | clear -AI HCUR0 CR2; lia| clear -ASH HCUR0 CR2; lia| clear -AFR HCUR0 CR2; lia| exact HDR| exact LS1| clear -LS2; lia| exact MI]. }
      intros ms1 (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s21 & t31 & t41 & t51 & t61 & nws1 & m1 & E1 & MUI' & WMI' & MI1
                   & KSS1 & FRS1 & SCW1 & LLC1 & AST1 & HDR1 & MAP1 & NA1 & KR1 & IND1 & HP).
      subst ms1.
      assert (MU1 : munchW W m0 m1).
      { unfold munchW in *. eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MUI'].
        intros xx Hxx. pose proof (HW_fix xx Hxx) as Hf. pose proof (HW_map EH xx Hxx) as Hmp. pose proof (HWI odr (or_introl eq_refl) xx Hxx) as Ho.
        cbn [outside] in Hf, Hmp |- *. clear -Hf Hmp Ho HS1 HS2 HCUR0 CR2 HP. lia. }
      assert (WM1 : wmono bsegs m0 m1) by exact (wmono_trans bsegs m0 m m1 WM0 WMI').
      assert (INDS1 : forall o, In o (RGM.inds r) -> rw_cells bsegs m1 o [C1 (Z_to_bv 8 0)]).
      { intros o Ho. pose proof (HOW o (or_intror Ho)) as OW. assert (NEo : o <> odr) by (intros ->; contradiction).
        apply (rw_cells_transport bsegs _ m m1 o _ (INDS o (or_intror Ho)) MUI' WMI').
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear -OW NEo SPlo SHL SHH AI HBI HCUR0 CR2 HP HN. lia. }
      eapply evt_mono.
      { eapply (IH (i + 1) (RGM.upd ks (Z.to_nat p) odr) (ne + 1) ks' ne' (cur + 32) (lsize + 1) (cur + 16)); try eassumption.
        - clear -Hi; lia. - clear -Hin; lia.
        - intros o Ho. exact (HWI o (or_intror Ho)).
        - intros o Ho. exact (HOW o (or_intror Ho)).
        - intros _. exact EH.
        - clear -HCUR0; lia. - clear -HCUR; lia. - clear -LS1; lia. - clear -LS2; lia.
        - intros _. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [clear -M5; lia|].
          apply Forall_upd; [exact M6| clear -EOD; lia]. }
      intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s6' & s7' & t3' & t4' & t5' & t6' & nws' & m' & E & P1 & P2 & P3 & P4 & P5 & P6).
      exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s2', s6', s7', t3', t4', t5', t6', nws', m'.
      split; [replace (i + (1 + Z.of_nat (length r))) with (i + 1 + Z.of_nat (length r)) by lia; exact E|].
      split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      split; [| exact P6].
      replace (lsize + (1 + Z.of_nat (length r))) with (lsize + 1 + Z.of_nat (length r)) by lia.
      unfold first_after in *. destruct r as [|d2 r2]; [| exact P5].
      change (RGM.nind []) with 0 in HCUR. cbn [length Z.of_nat] in HCUR. replace (CEND - 16) with (cur + 16) by (clear -HCUR; lia). exact P5.
    + (* [comment removed for export] *)
      assert (EO : odr = RGM.ODR_NONE) by (unfold RGM.is_ind in EI; cbn [RGM.d_odr] in EI; apply negb_false_iff, Z.eqb_eq in EI; exact EI).
      subst odr.
      destruct (inds_cons_common _ r EI) as [EIND ENI]. rewrite EIND in *. rewrite ENI in *.
      assert (CR1 : cur + 16 <= CEND) by (clear -HCUR NN; lia).
      eapply evt_cut.
      { eapply (reg_iter_common fp n gp tp s3 s10 F fc i g beg size swr lend cur CEND lsize first);
        [exact Hi| clear -Hin; lia| exact Hn| reflexivity| exact REC| exact RDYN| exact RODR
        | exact B0| exact B8| exact S8| exact Z1| exact RU| exact SW| exact BT
        | exact AIN| exact RG| exact DO| exact PP| exact SHC| exact CP| exact MSC| exact AL| exact NS| exact MP
        | exact FRS| exact SPlo| exact FPhi| exact SCW| exact LLC| exact C01| exact CR1| exact HCE| exact HLE| exact AST
        | clear -AI HCUR0 CR1; lia| clear -ASH HCUR0 CR1; lia| clear -AFR HCUR0 CR1; lia| exact HDR| exact LS1| clear -LS2; lia| exact MI]. }
      intros ms1 (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s21 & t31 & t41 & t51 & t61 & m1 & E1 & MUI' & WMI' & MI1
                   & FRS1 & SCW1 & LLC1 & AST1 & HDR1).
      subst ms1.
      assert (MU1 : munchW W m0 m1).
      { unfold munchW in *. eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MUI'].
        intros xx Hxx. pose proof (HW_fix xx Hxx) as Hf. cbn [outside] in Hf |- *. clear -Hf HS1 HS2 HCUR0 CR1. lia. }
      assert (WM1 : wmono bsegs m0 m1) by exact (wmono_trans bsegs m0 m m1 WM0 WMI').
      assert (INDS1 : forall o, In o (RGM.inds r) -> rw_cells bsegs m1 o [C1 (Z_to_bv 8 0)]).
      { intros o Ho. pose proof (HOW o Ho) as OW.
        apply (rw_cells_transport bsegs _ m m1 o _ (INDS o Ho) MUI' WMI').
        cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear -OW SPlo SHL SHH AI HCUR0 CR1. lia. }
      assert (KSS1 : stk bsegs m1 (fp + -4264) (fp + -4256)).
      { apply (stk_transport_disjoint bsegs _ m m1 _ _ KSS MUI' WMI'). cbn [disjoint_from]. clear -SPlo SHH AFR HCUR0 CR1. lia. }
      assert (HM1 : hm = true -> rw_cells bsegs m1 MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
                /\ u64arr bsegs m1 B nws /\ keys_rep (Z.to_nat N) nws ks /\ 0 <= ne /\ Forall (fun k => 0 <= k < 2 ^ 64) ks).
      { intros EH. destruct (HM EH) as (M2 & M3 & M4 & M5 & M6). destruct (HMAP EH) as (HN & HB0 & HBT & HBI & HBS & HBC & HBF).
        assert (HLnw : length nws = (4 * Z.to_nat N)%nat) by (destruct M4 as (L & _); exact L).
        split; [| split; [| auto]].
        - apply (rw_cells_transport bsegs _ m m1 _ _ M2 MUI' WMI').
          cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear -SPlo SHL SHH AI HCUR0 CR1. lia.
        - apply (u64arr_transport bsegs _ m m1 B nws M3 MUI' WMI'). cbn [disjoint_from]. rewrite HLnw.
          clear -HN HB0 HBT HBI HBS HBC HBF SPlo SHL SHH HCUR0 CR1. lia. }
      eapply evt_mono.
      { eapply (IH (i + 1) ks ne ks' ne' (cur + 16) (lsize + 1) cur nws); try eassumption.
        - clear -Hi; lia. - clear -Hin; lia. - clear -HCUR0; lia. - clear -HCUR; lia. - clear -LS1; lia. - clear -LS2; lia. }
      intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s6' & s7' & t3' & t4' & t5' & t6' & nws' & m' & E & P1 & P2 & P3 & P4 & P5 & P6).
      exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', s2', s6', s7', t3', t4', t5', t6', nws', m'.
      split; [replace (i + (1 + Z.of_nat (length r))) with (i + 1 + Z.of_nat (length r)) by lia; exact E|].
      split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      split; [| exact P6].
      replace (lsize + (1 + Z.of_nat (length r))) with (lsize + 1 + Z.of_nat (length r)) by lia.
      unfold first_after in *. destruct r as [|d2 r2]; [| exact P5].
      change (RGM.nind []) with 0 in HCUR. cbn [length Z.of_nat] in HCUR. replace (CEND - 16) with cur by (clear -HCUR; lia). exact P5.
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto.
Qed.

Lemma outside_ind_fp : forall ds o x, In o (RGM.inds ds) -> outside (RGM.ind_fp ds) x -> ~ (o <= x < o + 1).
Proof.
  intros ds o x. unfold RGM.ind_fp. induction (RGM.inds ds) as [|o1 l IH]; intros Ho Hx; [destruct Ho|].
  cbn [map outside] in Hx. destruct Ho as [->|Ho]; [tauto| apply IH; tauto].
Qed.

Lemma outside_ind_fp_intro : forall ds x, (forall o, In o (RGM.inds ds) -> ~ (o <= x < o + 1)) -> outside (RGM.ind_fp ds) x.
Proof.
  intros ds x. unfold RGM.ind_fp. induction (RGM.inds ds) as [|o1 l IH]; intros H; cbn [map outside]; [exact I|].
  split; [apply H; left; reflexivity| apply IH; intros o Ho; apply H; right; exact Ho].
Qed.

(* [comment removed for export] *)
Lemma sh_lo_ge : forall y ds acc L, L <= acc -> Forall (fun d => L <= RGM.sh_lo1 y d) ds -> L <= RGM.sh_lo y ds acc.
Proof. intros y ds. induction ds as [|d r IH]; intros acc L HL HF; cbn [RGM.sh_lo]; [exact HL|]. inversion HF; subst. apply IH; [lia| assumption]. Qed.
Lemma sh_hi_le : forall y ds acc L, acc <= L -> Forall (fun d => RGM.sh_hi1 y d <= L) ds -> RGM.sh_hi y ds acc <= L.
Proof. intros y ds. induction ds as [|d r IH]; intros acc L HL HF; cbn [RGM.sh_hi]; [exact HL|]. inversion HF; subst. apply IH; [lia| assumption]. Qed.

Lemma run_sh_window : forall ds, ds <> [] -> forallb (RGM.d_okb B_RGL) ds = true ->
  0x7fffa000 <= RGM.run_sh_lo B_RGL ds /\ RGM.run_sh_hi B_RGL ds <= 0x80177a00.
Proof.
  intros ds NE OK. rewrite forallb_forall in OK.
  assert (FA : Forall (fun d => 0x7fffa000 <= RGM.sh_lo1 B_RGL d /\ RGM.sh_hi1 B_RGL d <= 0x80177a00) ds).
  { apply Forall_forall. intros d Hd. destruct (d_okb_A d (OK d Hd)) as (B0 & B8 & S8 & Z1 & RU & SW & BT & _).
    unfold RGM.sh_lo1, RGM.sh_hi1, RGM.shad. cbn [B_RGL RGM.l_shb]. split; Z.div_mod_to_equations; lia. }
  destruct ds as [|d r]; [contradiction|]. cbn [RGM.run_sh_lo RGM.run_sh_hi]. inversion FA as [|d0 r0 [F1 F2] FR]; subst.
  split; [apply sh_lo_ge; [exact F1| eapply Forall_impl; [| exact FR]; cbn; tauto]| apply sh_hi_le; [exact F2| eapply Forall_impl; [| exact FR]; cbn; tauto]].
Qed.

Theorem xr_regrun_spec : RGS.walk_stmt bsegs B_RGC.
Proof.
  unfold RGS.walk_stmt.
  intros i n ds N ne ks ks' ne' B cur lend size first fp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2 s3 s6 s7 s10 F fc m.
  intros RUN K1 I0 IK NT HD ND INDS AIN RG PP DO SHC CP MSC AL NS MP KSS FRS FP16 SPI SPS FPH SCW LLC C0 CE LE AST AIm ASHm AFRm HDR LS1 LS2 HMP MI.
  (* [comment removed for export] *)
  set (k := Z.of_nat (length ds)) in *. set (na := k + RGM.nind ds) in *.
  set (hm := 0 <? RGM.nind ds) in *.
  set (W := [(fp - 0x10a8, fp - 0x10a0); (fp - 0x10f0 - 32, fp - 0x10f0); (RGM.run_sh_lo (RGM.c_lay B_RGC) ds, RGM.run_sh_hi (RGM.c_lay B_RGC) ds);
             (RGM.c_statics B_RGC + 8, RGM.c_statics B_RGC + 24); (RGM.c_lla B_RGC + 8, RGM.c_lla B_RGC + 16); (cur, cur + 16 * na)]
            ++ RGM.ind_fp ds ++ (if hm then [(RGM.c_map B_RGC + 8, RGM.c_map B_RGC + 12); (B, B + 32 * N)] else [])).
  change (RGM.shad (RGM.c_lay B_RGC) (RGM.l_ilo (RGM.c_lay B_RGC))) with SHW_LO in *.
  change (RGM.shad (RGM.c_lay B_RGC) (RGM.l_ihi (RGM.c_lay B_RGC))) with SHW_HI in *.
  change (RGM.c_flags B_RGC + 24) with 0x6a1290 in *. change (RGM.c_flags B_RGC + 85) with 0x6a12cd in *. change (RGM.c_flags B_RGC + 100) with 0x6a12dc in *.
  change (RGM.c_statics B_RGC + 8) with 0x6a12f8 in *. change (RGM.c_statics B_RGC + 24) with 0x6a1308 in *. change (RGM.c_statics B_RGC + 56) with 0x6a1328 in *.
  change (RGM.c_lay B_RGC) with B_RGL in *.
  cbn [B_RGC RGM.c_entry RGM.c_tab RGM.c_inited RGM.c_flags RGM.c_shcell RGM.c_canpoison RGM.c_msetcell RGM.c_memset RGM.c_llaalign
       RGM.c_lla RGM.c_statics RGM.c_map RGM.c_tabend] in *.
  change (RGM.l_ilo B_RGL) with 0x10000 in *. change (RGM.l_ihi B_RGL) with 0xbfd000 in *. change (RGM.l_shb B_RGL) with 0x7fff8000 in *.
  replace (fp - 4272) with (fp + -4272) in NS by lia. replace (fp - 4304) with (fp + -4304) in MP by lia.
  replace (fp - 4264) with (fp + -4264) in KSS by lia. replace (fp - 4256) with (fp + -4256) in KSS by lia.
  pose proof (RGM.run_ok _ _ _ _ _ _ RUN) as OKS.
  assert (DNE : ds <> []) by (intros ->; subst k; cbn in K1; lia).
  destruct (run_sh_window ds DNE OKS) as [SWL SWH].
  pose proof (RGM.run_sh_hull B_RGL ds) as HULL.
  pose proof (RGM.inds_window B_RGL ds OKS) as IW. cbn [B_RGL RGM.l_odr_lo RGM.l_odr_hi] in IW.
  pose proof (nind_nonneg ds) as NN.
  (* [comment removed for export] *)
  assert (GEO : hm = true -> 8 <= N <= 2 ^ 20 /\ 0 < B /\ B + 32 * N <= 2 ^ 47 /\ (B + 32 * N <= 0x10000 \/ 0xbfd000 <= B)
                               /\ (B + 32 * N <= SHW_LO \/ SHW_HI <= B) /\ (B + 32 * N <= cur \/ cur + 16 * na <= B)
                               /\ (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B)).
  { intros EH. unfold hm in EH. apply Z.ltb_lt in EH. destruct (HMP EH) as (_ & _ & G1 & _ & _ & _ & _ & _ & G2 & G3 & G4 & _ & G5 & G6 & G7).
    repeat split; try assumption; try lia. }
  assert (MAPF : exists nws, hm = true -> rw_cells bsegs m MAPA [C8 (Z_to_bv 64 B); C4 (Z_to_bv 64 ne); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 N)]
                /\ u64arr bsegs m B nws /\ keys_rep (Z.to_nat N) nws ks /\ 0 <= ne /\ Forall (fun key => 0 <= key < 2 ^ 64) ks).
  { destruct hm eqn:EHM; [| exists []; intros X; discriminate X].
    apply Z.ltb_lt in EHM. destruct (HMP EHM) as (_ & M2 & HN & Hne & HLk & KF & KEYS & STKB & HB0 & HBT & _).
    destruct (stk_carve bsegs m B (B + 32 * N) (Z.to_nat (32 * N)) STKB ltac:(lia)) as [_ (junkn & NEWC)].
    replace (B + 32 * N - Z.of_nat (Z.to_nat (32 * N))) with B in NEWC by lia.
    destruct (u64arr_of_CB bsegs m B (4 * Z.to_nat N) _ _ NEWC ltac:(lia)) as (nws & HLw & NA).
    exists nws. intros _. split; [exact M2|]. split; [exact NA|]. split; [| split; [exact Hne| exact KF]].
    split; [exact HLw|]. split; [lia|]. intros d Hd.
    destruct (nth_error nws (4 * d)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
    f_equal. replace (4 * d)%nat with (Z.to_nat (4 * Z.of_nat d)) in Hw by lia.
    pose proof (KEYS (Z.of_nat d) ltac:(lia)) as RC. rewrite Nat2Z.id in RC.
    replace (B + 32 * Z.of_nat d) with (B + 8 * (4 * Z.of_nat d)) in RC by lia.
    exact (u64arr_key_word m B nws _ w _ NA Hw ltac:(lia) RC). }
  destruct MAPF as (nws & HMm).
  assert (MPCm : hm = true -> rw_cells bsegs m 0x6a1328 [C8 (Z_to_bv 64 MAPA)]).
  { intros EH. unfold hm in EH. apply Z.ltb_lt in EH. destruct (HMP EH) as (M1 & _). exact M1. }
  eapply evt_mono.
  { eapply (reg_loop fp n gp tp s3 s10 F fc B N hm W m (RGM.run_sh_lo B_RGL ds) (RGM.run_sh_hi B_RGL ds) cur (cur + 16 * na) lend);
      try eassumption.
    - (* [comment removed for export] *)
      intros x Hx. unfold W in Hx. apply outside_app in Hx as [H6 _]. cbn [outside B_RGC RGM.c_lla RGM.c_statics RGM.c_map] in H6 |- *. clear -H6. lia.
    - intros EH x Hx. unfold W in Hx. apply outside_app in Hx as [_ Hx]. apply outside_app in Hx as [_ Hx]. rewrite EH in Hx.
      cbn [outside B_RGC RGM.c_lla RGM.c_statics RGM.c_map] in Hx |- *. exact Hx.
    - (* [comment removed for export] *)
      intros x Hx. unfold W. apply outside_app. split; [| apply outside_app; split].
      + cbn [outside B_RGC RGM.c_lla RGM.c_statics RGM.c_map]. unfold ro_area in Hx. clear -Hx SPS SWL SWH AIm AFRm FPH.
        lia.
      + apply outside_ind_fp_intro. intros o Ho. pose proof (IW o Ho) as OW. unfold ro_area in Hx. clear -Hx OW SPS. lia.
      + destruct hm eqn:EHM; [| exact I]. cbn [outside B_RGC RGM.c_lla RGM.c_statics RGM.c_map]. destruct (GEO eq_refl) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
        unfold ro_area in Hx. clear -Hx G1 G2 G4 G7 SPS. lia.
    - intros o Ho x Hx. unfold W in Hx. apply outside_app in Hx as [_ Hx]. apply outside_app in Hx as [Hx _]. exact (outside_ind_fp ds o x Ho Hx).
    - intros H. unfold hm. apply Z.ltb_lt. exact H.
    - lia.
    - unfold na, k. reflexivity.
    - unfold munchW. apply munch_refl.
    - apply wmono_refl. }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s6' & s7' & t3' & t4' & t5' & t6' & nws' & m' & E & P1 & P2 & P3 & P4 & P5 & P6).
  exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', s2', s6', s7', m'.
  split; [rewrite E; reflexivity|].
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact (xr_rw_cells_app_r m' LLA [C8 _] [C8 _] P4)|].
  split.
  { unfold first_after in P5. destruct ds as [|d0 r0]; [contradiction|]. exact P5. }
  intros EH. assert (EHM : hm = true) by (unfold hm; apply Z.ltb_lt; exact EH).
  destruct (P6 EHM) as (Q1 & Q2 & Q3). destruct (GEO EHM) as (G1 & _).
  split.
  - exact (xr_rw_cells_app_l m' (MAPA + 8) [C4 _] [C4 _] (xr_rw_cells_app_l m' (MAPA + 8) [C4 _; C4 _] [C4 _] (xr_rw_cells_app_r m' MAPA [C8 _] _ Q1))).
  - intros b Hb. destruct Q3 as (L3 & _ & K3).
    replace (B + 32 * b) with (B + 8 * (4 * b)) by lia.
    apply (u64arr_cell m' B nws' (4 * b) _ Q2); [| lia].
    replace (Z.to_nat (4 * b)) with (4 * Z.to_nat b)%nat by lia. apply K3. lia.
Qed.
