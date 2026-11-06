(* fm's strncasecmp runtime contract in the donor's form: `astrncasecmp_realizes` (lib/A/FMH_Rt.v) at PC_strncasecmp.
   No new walk. The machine half is the Bz body walk of the interceptor, already proved at fm.asan's addresses:
   the trampoline 0x412d8 (A/Bz/A/I_tramp.v tramp_strncasecmp) and __interceptor_strncasecmp 0x423a0
   (A/Bz/A/I_scase.v istrncasecmp_spec, with A/Bz/A/R_isPoisoned.v rip_proof). This file reads the walk's local
   premises off the donor's call-site state (AR, ecall_pre_k, cstr_ok, rom_viewN/rom_viewO; TfibSyms for the runtime
   cells), RUNS the walk on the cleaned store (A/FMbz_clean.v bz_run_clean: the donor gives no `mem_inv`, so the walk
   runs where it holds and the result transfers), and reads its post back into rt_post_ro: AR kept through
   AR_laws (Reusable/YG0q.v AR_laws_ok), the answer through A/FMspec_str.v (scase_res_z, zcase_res_zero). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YK14.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m FMupoison FMH_Base FMH_Rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require AF0x AB13 FMbz_bridge FMbz_str FMspec_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMbz_clean FMrt_lift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib Require Exec Mem Frame Cells Step MState ImageA.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A Require
  I_scasem I_scase I_strncmpw I_strncmpw3 I_qck I_consts R_m2s I_tramp R_isPoisoned.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Regs6ss RegisterBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.Frame.
Module BzC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.Cells.
Module BzS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.Step.
Module BzMS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.MState.
Module BzI := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.Lib.ImageA.
Module SCM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_scasem.
Module SCS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_scase.
Module SW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strncmpw.
Module SW3 := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strncmpw3.
Module QK := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_qck.
Module ICN := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_consts.
Module M2S := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_m2s.
Module TRP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.
Module LR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Regs6ss.
Module LRB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.RegisterBridge.
Module FB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMbz_bridge.
Module FS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMbz_str.
Module FP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMspec_str.

(* ---- the functional half: the walk's answer on the program part's byte lists ---- *)

Lemma nul_last_cstr : forall l, Forall (fun c => c <> 0) l -> Forall (fun c => 0 <= c < 256) l ->
  FP.nul_last (l ++ [0]).
Proof. intros l Hz Hr. exists l. split; [reflexivity | split; assumption]. Qed.

Lemma nul_last_len : forall m, FP.nul_last m -> (1 <= length m)%nat.
Proof. intros m (l & -> & _). rewrite length_app. cbn [length]. lia. Qed.

(* the walk stops at the first NUL at the latest, so its stop index is inside both strings *)
Lemma zcase_idx_lt : forall k m1 m2, FP.nul_last m1 -> FP.nul_last m2 ->
  (FP.zcase_idx k m1 m2 < length m1)%nat /\ (FP.zcase_idx k m1 m2 < length m2)%nat.
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  - cbn [FP.zcase_idx]. pose proof (nul_last_len m1 N1). pose proof (nul_last_len m2 N2). lia.
  - destruct m1 as [|x r1]; [pose proof (nul_last_len [] N1) as L; cbn in L; lia|].
    destruct m2 as [|y r2]; [pose proof (nul_last_len [] N2) as L; cbn in L; lia|].
    cbn [FP.zcase_idx length].
    destruct (negb (SCM.zlw x =? SCM.zlw y) || (x =? 0))%bool eqn:EB; [lia|].
    apply orb_false_iff in EB as [EL EX]. apply negb_false_iff, Z.eqb_eq in EL. apply Z.eqb_neq in EX.
    assert (Hx0 : 0 <= x < 256) by exact (FP.nul_last_hd_range x r1 N1).
    assert (HY : y <> 0) by (intros ->; apply EX; apply FP.lc_zero; [lia | rewrite EL; reflexivity]).
    destruct (IH r1 r2 (FP.nul_last_tl x r1 N1 EX) (FP.nul_last_tl y r2 N2 HY)) as [L1 L2].
    lia.
Qed.

Lemma zcase_res_range : forall k m1 m2,
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  (FP.zcase_idx k m1 m2 < length m1)%nat -> (FP.zcase_idx k m1 m2 < length m2)%nat ->
  -256 < FP.zcase_res k m1 m2 < 256.
Proof.
  intros k m1 m2 R1 R2 L1 L2. unfold FP.zcase_res. cbv zeta.
  set (i := FP.zcase_idx k m1 m2) in *.
  destruct (Nat.eqb i k); [lia|].
  assert (H1 : 0 <= nth i m1 0 < 256) by (apply (proj1 (Forall_forall _ _) R1); apply nth_In; exact L1).
  assert (H2 : 0 <= nth i m2 0 < 256) by (apply (proj1 (Forall_forall _ _) R2); apply nth_In; exact L2).
  pose proof (SCM.zlw_range _ H1). pose proof (SCM.zlw_range _ H2). lia.
Qed.

(* what the interceptor walk needs of its two strings, and what its answer means (FMH_Rt.v:27 strncase_eq) *)
Lemma ncase_facts : forall n l1 l2, 0 <= n ->
  Forall (fun c => c <> 0) l1 -> Forall (fun c => 0 <= c < 256) l1 ->
  Forall (fun c => c <> 0) l2 -> Forall (fun c => 0 <= c < 256) l2 ->
  SCM.scase_ok n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) /\
  0 <= SCM.scase_sz n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) /\
  SCM.scase_sz n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) <= Z.of_nat (length l1) + 1 /\
  SCM.scase_sz n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) <= Z.of_nat (length l2) + 1 /\
  -256 < SCM.scase_res n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) < 256 /\
  (SCM.scase_res n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0])) = 0 <->
   strncase_eq (Z.to_nat n) l1 l2).
Proof.
  intros n l1 l2 Hn Z1 R1 Z2 R2.
  pose proof (nul_last_cstr l1 Z1 R1) as N1. pose proof (nul_last_cstr l2 Z2 R2) as N2.
  assert (R1' : Forall (fun c => 0 <= c < 256) (l1 ++ [0]))
    by (apply Forall_app; split; [exact R1 | constructor; [lia | constructor]]).
  assert (R2' : Forall (fun c => 0 <= c < 256) (l2 ++ [0]))
    by (apply Forall_app; split; [exact R2 | constructor; [lia | constructor]]).
  destruct (zcase_idx_lt (Z.to_nat n) _ _ N1 N2) as [L1 L2].
  pose proof (zcase_res_range _ _ _ R1' R2' L1 L2) as RNG.
  assert (ER : SCM.scase_res n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
               = FP.zcase_res (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0]))
    by (apply FP.scase_res_z; assumption).
  assert (EI : SCM.scase_idx n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
               = Z.of_nat (FP.zcase_idx (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0])))
    by (unfold SCM.scase_idx; rewrite (FP.scase_idx_aux_z _ _ _ R1' R2'); reflexivity).
  unfold SCM.scase_ok, SCM.scase_sz. rewrite EI, ER, !length_map.
  rewrite length_app in L1, L2 |- *. rewrite length_app. cbn [length] in L1, L2 |- *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact RNG|].
  rewrite (FP.zcase_res_zero _ _ _ N1 N2). unfold strncase_eq. rewrite FP.lc_is_zlw. reflexivity.
Qed.

Lemma bv0_iff : forall r, -256 < r < 256 -> (bv_unsigned (Z_to_bv 64 r) = 0 <-> r = 0).
Proof.
  intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  split; [intros H | intros ->; reflexivity]. Z.div_mod_to_equations. lia.
Qed.

(* ---- the memory half: the donor's string premises as the walk's byte lists ---- *)

Lemma garr8_bytes : forall m p l, garr8 tfibsegs m p l -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  BzM.bytes_at BzI.asegs m p (map (Z_to_bv 8) l) /\ Forall (fun c => 0 <= c < 256) l.
Proof.
  intros m p l Hg Hp Hl. split.
  - split; [exact Hp|]. split; [rewrite length_map; exact Hl|].
    intros i Hi. rewrite length_map in Hi. destruct (Hg i Hi) as (Hv & Hr).
    specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
    rewrite YI04.le_byte_small in Hv by (first [lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia]).
    change (8 * Z.of_nat 0) with 0 in Hv. rewrite Z.shiftr_0_r in Hv.
    rewrite <- FS.mbyte_mrd, Hv, (FP.nth_error_map_nth l i Hi). reflexivity.
  - apply Forall_forall. intros c Hc. destruct (In_nth l c 0 Hc) as (i & Hi & <-). exact (proj2 (Hg i Hi)).
Qed.

(* chk_ok of a prefix of a cstr_ok string (FMH_Base.v cstr_ok): the interceptor's range check *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma chk_of_cstr : forall ly S W mem md p len sz, AR tfibsegs B ly S W mem md ->
  4096 <= p -> p + len + 8 <= alloc_ceiling -> 0 <= len < 2 ^ 40 -> amem_range p (len + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p (len + 1) ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) p (len + 1) -> 0 <= sz <= len + 1 ->
  QK.chk_ok (mrestrict (w_H W) mem) p sz.
Proof.
  intros ly S W mem md p len sz HAR Hp Hc Hl Ham HRA HHV Hsz.
  pose proof alloc_ceiling_value as (HCV & _).
  destruct (Z.eq_dec sz 0) as [->|NZ].
  - split; [intros i Hi; lia|]. split; intros Hn; lia.
  - apply (FS.chk_ok_of_AR B ly S W mem md p sz HAR); try lia.
    + unfold ICN.region_in_mem, amem_range in *.
      unfold M2S.kLowMemEnd, M2S.kHighShadowEnd, M2S.kHighMemEnd.
      unfold YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in Ham. lia.
    + intros z Hz. apply HRA. lia.
    + intros s Hs. apply HHV. unfold shadow_addr in *.
      assert (A1 : (p + sz - 1) / 8 <= (p + (len + 1) - 1) / 8) by (apply Z.div_le_mono; lia).
      assert (A2 : (SHADOW_OFF + (p + sz - 1) / 8) / 8 <= (SHADOW_OFF + (p + (len + 1) - 1) / 8) / 8)
        by (apply Z.div_le_mono; lia).
      lia.
Qed.

End k.

(* ---- the machine half: a walk on the canonical register map is a walk on any equal one ---- *)

Lemma bz_msteps_eqv : forall segs ms fin, BzE.msteps segs ms fin -> forall ms', LR.ms_eqv ms ms' ->
  exists fin', BzE.msteps segs ms' fin' /\ LR.ms_eqv fin fin'.
Proof.
  intros segs ms fin Hs. induction Hs as [ms | ms mid fin [HP HS] _ IH]; intros ms' HE.
  - exists ms'. split; [apply BzE.msteps_refl | exact HE].
  - pose proof (LRB.step_register_eqv segs ms ms' HE) as K. rewrite HS in K.
    destruct (RiscvSemantics.step segs ms') as [mid'| |] eqn:E; cbn [LR.res_eqv] in K; try contradiction.
    destruct (IH mid' K) as (fin' & HT & HF). exists fin'. split; [|exact HF].
    eapply BzE.msteps_cons; [|exact HT]. split; [|exact E].
    destruct HE as (_ & _ & _ & Hsvc & _). rewrite <- Hsvc. exact HP.
Qed.

Lemma bz_evt_eqv : forall segs (P : machine_state -> Prop) ms ms', LR.ms_eqv ms ms' -> BzE.evt segs P ms ->
  BzE.evt segs (fun a => exists c, P c /\ LR.ms_eqv c a) ms'.
Proof.
  intros segs P ms ms' HE (fin & HS & HP).
  destruct (bz_msteps_eqv segs ms fin HS ms' HE) as (fin' & HS' & HF).
  exists fin'. split; [exact HS' | exists fin; split; assumption].
Qed.

Section r. Context {fx : YK11.FPState}.

Lemma getr_xregs : forall R R', LR.xregs_eqv R R' -> forall q, getr R' q = getr R q.
Proof.
  intros R R' HX q. unfold getr. destruct (bv_eqb q 0) eqn:E; [reflexivity|].
  symmetry. apply HX. exact E.
Qed.

End r.

Lemma mod2_land64 : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma land_m2_mod2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

(* the return address the donor's ecall_pre carries (ret_ok) is where the walk's `ret` lands *)
Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> BzMS.ret_pc k = k.
Proof.
  intros k Hk. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, mod2_land64; apply land_m2_mod2).
  rewrite <- (BzMS.Z_to_bv_bv_unsigned k). apply BzMS.ret_pc_even; [exact Hr | exact Hm].
Qed.

(* ---- the runtime cells the interceptor reads, from AR's constant cells (fm's Tfib_const, A/AF0m.v) ---- *)

(* the absolute constant cell covering a, and its byte there *)
Fixpoint clook (l : list acell) (a : Z) : option Z :=
  match l with
  | [] => None
  | c :: t =>
      match c_at c, c_val c with
      | ANum a0, AV (ANum v) =>
          if ((a0 <=? a) && (a <? a0 + Z.of_nat (c_w c)))%bool then Some (le_byte v (c_w c) (Z.to_nat (a - a0)))
          else clook t a
      | _, _ => clook t a
      end
  end.

Lemma clook_sound : forall l a r, clook l a = Some r ->
  exists c a0 v, In c l /\ c_at c = ANum a0 /\ c_val c = AV (ANum v) /\ a0 <= a < a0 + Z.of_nat (c_w c) /\
    r = le_byte v (c_w c) (Z.to_nat (a - a0)).
Proof.
  intros l. induction l as [|c t IH]; intros a r H; cbn [clook] in H; [discriminate|].
  assert (Rest : clook t a = Some r -> exists c' a0 v, In c' (c :: t) /\ c_at c' = ANum a0 /\
    c_val c' = AV (ANum v) /\ a0 <= a < a0 + Z.of_nat (c_w c') /\ r = le_byte v (c_w c') (Z.to_nat (a - a0))).
  { intros Ht. destruct (IH a r Ht) as (c' & a0 & v & Hin & R). exists c', a0, v. split; [right; exact Hin | exact R]. }
  destruct c as [ca cw cv]. cbn [c_at c_val c_w] in H, Rest |- *.
  destruct ca; try exact (Rest H). destruct cv as [e|]; try exact (Rest H). destruct e; try exact (Rest H).
  match type of H with context [if ?b then _ else _] => destruct b eqn:EB end; [|exact (Rest H)].
  injection H as <-. apply andb_prop in EB as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  eexists (ACell _ cw _), _, _. split; [left; reflexivity|]. cbn [c_at c_val c_w].
  split; [reflexivity|]. split; [reflexivity|]. split; [lia | reflexivity].
Qed.

Definition cmatch (A : Z) (bs : list byte) : bool :=
  forallb (fun i => match clook Tfib_const_abs (A + Z.of_nat i), nth_error bs i with
                    | Some z, Some b => Z.eqb z (bv_unsigned b)
                    | _, _ => false
                    end) (seq 0 (length bs)).

(* the two cell groups the walk takes, on the cleaned store: each is read-only or writable image cells at fixed
   addresses, so A/FMbz_clean.v ro_cells_clean / rw_cells_clean carry it over; the writable ones need rw_range,
   a computation on fm.asan's segment table *)
Lemma icells_sc_clean : forall m, rom_eq m -> SW.icells_sc m -> SW.icells_sc (clean m).
Proof.
  intros m HE (C1 & C2 & C3 & C4 & C5).
  split; [| split; [| split; [| split]]].
  - apply (ro_cells_clean m _ _ HE); [cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia | exact C1].
  - apply (ro_cells_clean m _ _ HE); [cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia | exact C2].
  - apply (ro_cells_clean m _ _ HE); [cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia | exact C3].
  - apply (rw_cells_clean m _ _ HE); [lia | cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia
      | vm_compute; reflexivity | exact C4].
  - apply (ro_cells_clean m _ _ HE); [cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia | exact C5].
Qed.

Lemma m2s_cells_clean : forall m, rom_eq m -> M2S.m2s_cells m -> M2S.m2s_cells (clean m).
Proof.
  intros m HE (C1 & C2 & C3).
  split; [| split].
  - apply (rw_cells_clean m _ _ HE); [lia | cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia
      | vm_compute; reflexivity | exact C1].
  - apply (rw_cells_clean m _ _ HE); [lia | cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia
      | vm_compute; reflexivity | exact C2].
  - apply (rw_cells_clean m _ _ HE); [lia | cbn [BzC.cells_size BzC.csize]; unfold BzM.UTOP; lia
      | vm_compute; reflexivity | exact C3].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shared Section hypothesis of fm's program part (HarnessDesign): B is fm's TfibB *)
Hypothesis HB : TfibSyms B.

Lemma const_view : forall ly S W mem md a r, AR tfibsegs B ly S W mem md ->
  clook Tfib_const_abs a = Some r -> aview tfibsegs (w_H W) mem a = Some r.
Proof.
  intros ly S W mem md a r HAR Hl.
  destruct (clook_sound _ _ _ Hl) as (c & a0 & v & Hin & EA & EV & Ha & ->).
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (ts_const B HB) in HC.
  assert (Hin' : In c (Tfib_const ly))
    by (unfold Tfib_const; apply in_or_app; right; apply in_or_app; left; exact Hin).
  pose proof (proj1 (Forall_forall _ _) HC c Hin') as Hc. unfold cell_holds in Hc. cbv zeta in Hc.
  rewrite EA, EV in Hc. cbn [aeval] in Hc.
  specialize (Hc (Z.to_nat (a - a0)) ltac:(lia)).
  replace (a0 + Z.of_nat (Z.to_nat (a - a0))) with a in Hc by lia. exact Hc.
Qed.

Lemma bytes_of_consts : forall ly S W mem md A bs, AR tfibsegs B ly S W mem md ->
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 -> cmatch A bs = true ->
  BzM.bytes_at BzI.asegs (mrestrict (w_H W) mem) A bs.
Proof.
  intros ly S W mem md A bs HAR HA HL HM. split; [exact HA|]. split; [exact HL|].
  intros i Hi. unfold cmatch in HM. rewrite forallb_forall in HM.
  specialize (HM i (proj2 (in_seq (length bs) 0 i) ltac:(lia))). cbv beta in HM.
  destruct (clook Tfib_const_abs (A + Z.of_nat i)) as [z|] eqn:EC; [|discriminate].
  destruct (nth_error bs i) as [b|] eqn:EN; [|discriminate]. apply Z.eqb_eq in HM.
  pose proof (const_view ly S W mem md _ _ HAR EC) as HV. unfold aview in HV. rewrite FS.mbyte_mrd in HV.
  destruct (BzM.mrd BzI.asegs (mrestrict (w_H W) mem) (BzM.wa (A + Z.of_nat i))) as [b'|] eqn:EM;
    [|discriminate].
  cbn in HV. injection HV as HV. f_equal. apply bv_eq. lia.
Qed.

Ltac ro_c HAR :=
  split; [cbn; tauto
         | apply (bytes_of_consts _ _ _ _ _ _ _ HAR);
           [lia | apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity]].
Ltac wr_c :=
  split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi;
  apply AB13.tfib_rw_window; rewrite BzM.wa_unsigned by lia; lia.

Lemma icells_of_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
  SW.icells_sc (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md HAR. unfold SW.icells_sc, BzS.ro_cells, BzS.rw_cells, BzC.cells_at.
  split; [ro_c HAR|]. split; [ro_c HAR|]. split; [ro_c HAR|]. split; [split; [ro_c HAR | wr_c]|]. ro_c HAR.
Qed.

Lemma m2s_of_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
  M2S.m2s_cells (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md HAR. unfold M2S.m2s_cells, BzS.rw_cells, BzC.cells_at.
  split; [split; [ro_c HAR | wr_c]|]. split; [split; [ro_c HAR | wr_c] | split; [ro_c HAR | wr_c]].
Qed.

(* ---- the contract ---- *)

Theorem fm_astrncasecmp_realizes : astrncasecmp_realizes tfibsegs B PC_strncasecmp.
Proof.
  unfold astrncasecmp_realizes.
  intros ly S W regs mem md x y n l1 l2 HPRE HROM HSC G10 G11 G12 Hn C1 C2.
  destruct HPRE as (HEP & Hceil & HstkK & HpresK).
  destruct HEP as (HAR & Hra & Hal16 & Hslo & Hshi & HpresE & Hgp & Htp).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  pose proof alloc_ceiling_value as (HCV & _).
  unfold STK_RT_STR, ESTACK in *.
  destruct C1 as ((Hg1 & Hnz1) & Hp1 & Hc1 & Hl1 & Ham1 & HRA1 & HHV1 & _).
  destruct C2 as ((Hg2 & Hnz2) & Hp2 & Hc2 & Hl2 & Ham2 & HRA2 & HHV2 & _).
  set (H := w_H W) in *. set (m := mrestrict H mem).
  set (sp0 := spZ regs) in *.
  (* the two strings as the walk's byte lists *)
  destruct (garr8_bytes m x (l1 ++ [0]) Hg1 ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia))
    as (B1 & R1).
  destruct (garr8_bytes m y (l2 ++ [0]) Hg2 ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia))
    as (B2 & R2).
  apply Forall_app in R1 as [R1 _]. apply Forall_app in R2 as [R2 _].
  destruct (ncase_facts n l1 l2 ltac:(lia) Hnz1 R1 Hnz2 R2) as (OK & SZ0 & SZ1 & SZ2 & RNG & EQV).
  set (b1 := map (Z_to_bv 8) (l1 ++ [0])) in *. set (b2 := map (Z_to_bv 8) (l2 ++ [0])) in *.
  set (sz := SCM.scase_sz n b1 b2) in *. set (r := SCM.scase_res n b1 b2) in *.
  assert (CK1 : QK.chk_ok m x sz)
    by (apply (chk_of_cstr B ly S W mem md x (Z.of_nat (length l1)) sz HAR); assumption || lia).
  assert (CK2 : QK.chk_ok m y sz)
    by (apply (chk_of_cstr B ly S W mem md y (Z.of_nat (length l2)) sz HAR); assumption || lia).
  (* the donor gives no `mem_inv`, so the walk runs on the cleaned store (A/FMbz_clean.v) *)
  assert (ROMEQ : rom_eq m) by exact (rom_eq_of_views B W mem HB HROM HSC).
  set (mc := clean m) in *.
  assert (B1c : BzM.bytes_at BzI.asegs mc x b1)
    by (apply (bytes_at_clean m x b1 ROMEQ); [unfold b1; rewrite length_map, length_app; cbn [length];
        unfold BzM.UTOP; lia | exact B1]).
  assert (B2c : BzM.bytes_at BzI.asegs mc y b2)
    by (apply (bytes_at_clean m y b2 ROMEQ); [unfold b2; rewrite length_map, length_app; cbn [length];
        unfold BzM.UTOP; lia | exact B2]).
  assert (CK1c : QK.chk_ok mc x sz) by (apply (chk_ok_clean m x sz ROMEQ); [lia | lia | exact CK1]).
  assert (CK2c : QK.chk_ok mc y sz) by (apply (chk_ok_clean m y sz ROMEQ); [lia | lia | exact CK2]).
  assert (STKc : BzF.stk BzI.asegs mc (sp0 - 8192) sp0)
    by (apply (stk_clean m (sp0 - 8192) sp0); [unfold AF0x.TFIB_IMG_END; lia | unfold BzM.UTOP; lia |
        exact (FB.stk_of_apresent H mem (sp0 - 8192) sp0 ltac:(lia) ltac:(lia) HpresK)]).
  assert (M2Sc : M2S.m2s_cells mc) by exact (m2s_cells_clean m ROMEQ (m2s_of_AR ly S W mem md HAR)).
  assert (ICc : SW.icells_sc mc) by exact (icells_sc_clean m ROMEQ (icells_of_AR ly S W mem md HAR)).
  (* the walk, from the canonical register map *)
  set (P := SW3.istrncmp_post (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9)
              (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (@fp_regs fx) (@fp_csr fx) r
              (sp0 - 8192) mc).
  set (c0 := BzMS.MS (BzF.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31))
             (@fp_regs fx) (Z_to_bv 64 0x412d8) (@fp_csr fx) None mc (seg_rom tfibsegs)).
  assert (WALK : BzE.evt BzI.asegs P c0).
  { unfold c0, P. apply TRP.tramp_strncasecmp.
    apply (SCS.istrncasecmp_spec RIP.rip_proof (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
             (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
             (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
             (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
             (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
             (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) mc x y n b1 b2 (sp0 - 8192));
      change (bv_unsigned (getr regs 2)) with sp0.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact STKc.
    - lia.
    - unfold M2S.kHighShadowEnd. lia.
    - lia.
    - lia.
    - exact B1c.
    - exact B2c.
    - exact OK.
    - lia.
    - lia.
    - left. lia.
    - left. lia.
    - exact CK1c.
    - exact CK2c.
    - exact M2Sc.
    - exact ICc.
    - exact (mem_inv_clean m). }
  assert (EQVC : LR.ms_eqv c0 (FMrt_lift.canon_at regs PC_strncasecmp mc)).
  { split; [intros q Hq; reflexivity | repeat split; reflexivity]. }
  apply (bz_run_clean B HB W PC_strncasecmp regs mem md (fun a => exists c, P c /\ LR.ms_eqv c a) _ HROM HSC).
  { exact (bz_evt_eqv BzI.asegs P c0 _ EQVC WALK). }
  (* the walk's end state msc (over the cleaned store) and the real end state ms', read back into rt_post_ro *)
  intros msc ms' model' (c & HP & HEc) Hclc HE Hsbm Hcl.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Ec & MU & WM & MI' & ST').
  subst c. change (bv_unsigned (getr regs 2)) with sp0 in MU, ST'.
  destruct HEc as (HXRc & HFRc & HPCc & HSVc & HRVc & HFCc & HMEc & HROc).
  unfold BzMS.MS in HXRc, HFRc, HPCc, HSVc, HRVc, HFCc, HMEc, HROc.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
    HXRc, HFRc, HPCc, HSVc, HRVc, HFCc, HMEc, HROc.
  (* the walk changed only its frame of the cleaned store and left that frame present; so the real store changed
     only that frame and left it present (A/FMbz_clean.v clean_window) *)
  assert (MOUT : forall w : word, ~ (sp0 - 2256 <= bv_unsigned w < sp0) -> ms_mem msc w = clean m w).
  { intros w Hw. rewrite <- HMEc. apply MU. cbn [BzF.outside]. split; [exact Hw | exact I]. }
  assert (MIN : forall a, sp0 - 2256 <= a < sp0 -> ms_mem msc (Z_to_bv 64 a) <> None).
  { intros a Ha E. rewrite <- HMEc in E. destruct ST' as (_ & _ & HS). destruct (HS a ltac:(lia)) as (_ & b & Hb).
    unfold BzM.wa, BzM.mrd in Hb. rewrite E in Hb.
    pose proof (AF0x.seg_rom_none_high a ltac:(unfold AF0x.TFIB_IMG_END; lia)) as HN.
    change (seg_rom tfibsegs (Z_to_bv 64 a) = Some b) in Hb. congruence. }
  destruct (clean_window m msc (sp0 - 2256) sp0 Hclc MOUT MIN) as (MO & MN).
  rewrite unrestrict_mem in MO, MN.
  destruct HE as (HXR & HFR & HPC & HSV & HRV & HFC & HME & HRO).
  destruct ms' as [rg fr pcv sv rv fcv mm rom'].
  unfold unrestrict in HXR, HFR, HPC, HSV, HRV, HFC, HME, HRO.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
    HXR, HFR, HPC, HSV, HRV, HFC, HME, HRO, Hcl.
  rewrite <- HFRc in HFR. rewrite <- HPCc in HPC. rewrite <- HSVc in HSV. rewrite <- HRVc in HRV.
  rewrite <- HFCc in HFC. rewrite <- HROc in HRO.
  subst fr pcv sv rv fcv mm rom'.
  set (m2 := munrestrict Dc m (ms_mem msc)) in *.
  set (mem' := munrestrict H mem m2).
  assert (RM : forall w, mrestrict H mem' w = m2 w).
  { intros w. unfold mrestrict, mem', munrestrict. destruct (H w) eqn:EH; [symmetry; exact (Hcl w EH) | reflexivity]. }
  assert (MU' : forall w : word, ~ (sp0 - 2256 <= bv_unsigned w < sp0) -> m2 w = m w) by exact MO.
  assert (PR : forall w : word, sp0 - 2256 <= bv_unsigned w < sp0 -> exists b, m2 w = Some b).
  { intros w Hw. pose proof (MN (bv_unsigned w) Hw) as HN2. rewrite BzMS.Z_to_bv_bv_unsigned in HN2.
    destruct (m2 w) as [b|]; [exists b; reflexivity | exfalso; exact (HN2 eq_refl)]. }
  assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2256 <= a < sp0) ->
            aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hw. unfold aview, mbyte. rewrite RM. rewrite MU' by (rewrite BzMS.unsigned_lit by lia; exact Hw).
    reflexivity. }
  assert (VIS : forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H mem' a <> None).
  { intros a Hv. unfold aview, mbyte in *. rewrite RM.
    destruct (Z_le_gt_dec (sp0 - 2256) (bv_unsigned (Z_to_bv 64 a))) as [L|L];
      [destruct (Z_lt_ge_dec (bv_unsigned (Z_to_bv 64 a)) sp0) as [L'|L']|].
    - destruct (PR (Z_to_bv 64 a) ltac:(lia)) as (b & Eb). rewrite Eb. discriminate.
    - rewrite MU' by lia. exact Hv.
    - rewrite MU' by lia. exact Hv. }
  pose proof (same_but_materialized_frame md model' Hsbm)
    as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Heu).
  unfold rt_post_ro. split; [reflexivity|].
  exists rg, mem', model', (bv_unsigned (Z_to_bv 64 r)).
  split.
  { unfold cfg_at, unrestrict, mkst. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
    rewrite (ret_pc_ok _ Hra). unfold raZ, w64. rewrite BzMS.Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { apply (al_frame _ _ (AR_laws_ok tfibsegs B) ly S W mem md mem' model' HAR).
    - intros a Ha Hown. apply FR; [exact Ha|]. intros Hin.
      exact (al_stack _ _ (AR_laws_ok tfibsegs B) ly S W mem md a HAR ltac:(lia) Hown).
    - exact VIS.
    - exact Hvm.
    - exact Hlz.
    - exact Heu.
    - intros a _ Hh. change (w_H W) with H in Hh. unfold mem', munrestrict. rewrite Hh. reflexivity. }
  split.
  { intros q Hq. rewrite (getr_xregs _ _ HXR), (getr_xregs _ _ HXRc). unfold acallee_saved in Hq.
    destruct Hq as [->|[->|[->|[->|[->|Hq]]]]]; [reflexivity .. |].
    assert (Hq' : q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
      by lia.
    destruct Hq' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity. }
  split; [exact Hsbm|].
  split.
  { rewrite (getr_xregs _ _ HXR), (getr_xregs _ _ HXRc). unfold w64. rewrite BzMS.Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 r)) as HR. exact HR. }
  split.
  { rewrite <- EQV. exact (bv0_iff r RNG). }
  split.
  { intros a Ha Hw. apply FR; [exact Ha | lia]. }
  intros a (HHa & b & Hb). change (w_H W) with H in HHa. split; [exact HHa|].
  unfold mem', munrestrict. rewrite HHa.
  destruct (Z_le_gt_dec (sp0 - 2256) (bv_unsigned (Z_to_bv 64 a))) as [L|L];
    [destruct (Z_lt_ge_dec (bv_unsigned (Z_to_bv 64 a)) sp0) as [L'|L']|].
  - exact (PR (Z_to_bv 64 a) ltac:(lia)).
  - rewrite MU' by lia. exists b. unfold m, mrestrict. rewrite HHa. exact Hb.
  - rewrite MU' by lia. exists b. unfold m, mrestrict. rewrite HHa. exact Hb.
Qed.

End c.
