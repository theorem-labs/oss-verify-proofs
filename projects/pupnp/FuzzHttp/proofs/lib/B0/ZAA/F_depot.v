(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import ADepot ATacA ACells F_imemcpy F_depot_H F_depot_L F_depot_S.
Import ListNotations.
Open Scope Z_scope.

Definition depot_put_entry := 0x7851c%Z.

Lemma shl44_shr42 : forall h, 0 <= h < 2^64 -> Z.shiftr (Z.shiftl h 44 mod 18446744073709551616) 42 = 4 * bkt h.
Proof.
  intros h Hh. unfold bkt. rewrite Z.shiftl_mul_pow2 by lia.
  change 18446744073709551616 with (2^20 * 2^44). rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^44) with (4 * 2^42). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. lia.
Qed.

Lemma mm_fin_eq : forall v,
  Z.lxor ((((Z.lxor (((Z.lxor 0 v * MM_M) mod 18446744073709551616) ≫ 47) ((Z.lxor 0 v * MM_M) mod 18446744073709551616)) * MM_M) mod 18446744073709551616) ≫ 47)
         (((Z.lxor (((Z.lxor 0 v * MM_M) mod 18446744073709551616) ≫ 47) ((Z.lxor 0 v * MM_M) mod 18446744073709551616)) * MM_M) mod 18446744073709551616)
  = mm_fin v.
Proof. intros v. unfold mm_fin. rewrite Z.lxor_0_l, M64_eq. reflexivity. Qed.

Section PUT.
  Context {HC : HasCeiling}.
  Variable L : dlayout.
  Variables (ra gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q TR total : Z) (m0 : mem) (hs : list Z) (ws : list word) (tr : list Z).
  Notation n := (Z.of_nat (length tr)).
  Notation N := (zlen hs).
  Notation h := (depot_hash tr).
  Notation bp := (DT + 4 * bkt (depot_hash tr)).
  Notation nd := (DN0 L + 16 * (zlen hs + 1)).

  Notation W := [(q - 224, q); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                 (DN0 L + 16 * (zlen hs + 1), DN0 L + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                 (SS0 L + 8 * total, SS0 L + 8 * total + 8 + 8 * n)].

  Hypothesis DLO : dl_ok L.
  Hypothesis RD0 : RDEPOT L hs total m0.
  Hypothesis BUF : u64arr asegs m0 TR ws.
  Hypothesis TRW : firstn (length tr) ws = map wz tr.
  Hypothesis LEN : (length tr <= length ws)%nat.
  Hypothesis LTR : (1 <= length tr <= 30)%nat.
  Hypothesis RNG : Forall (fun x => 0 <= x < 2^64) tr.
  Hypothesis QTR : q <= TR.
  Hypothesis TRH : TR + 8 * Z.of_nat (length ws) <= 2^47.
  Hypothesis QAL : q mod 16 = 0.

  Hypothesis ROOM_N : 16 * (zlen hs + 2) <= 2^20.
  Hypothesis ROOM_F : 8 * (total + n + 1) <= SWIN L.
  Hypothesis ROOM_T : total + n + 1 < 2^20.
  Hypothesis MI0 : mem_inv asegs m0.

  Definition put_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists t0 t1 a1 a2 a3 a4 a5 a6 a7 m' (r : Z) hs' total',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo q /\ RDEPOT L hs' total' m' /\ u64arr asegs m' TR ws
      /\ ((r = dfind hs h /\ r <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs h = 0 /\ r = zlen hs + 1 /\ hs' = hs ++ [h] /\ total' = total + n + 1)).

  Definition put_mid (lo : Z) (t0 t1 : word) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 a5 a6 a7 m1 (j0 : list byte),
      let r := dfind hs h in let hd := head_of hs (bkt h) in
      ms' = MS (mkR ra (wz (q - 112)) gp tp t0 t1 t2 (wz 0) (wz DT) a0 a1 a2 (wz 4194312) (wz 0) a5 a6 a7
                    (wz bp) (wz h) (wz 5858336) s5 (wz 65535) (wz 2147483647) (wz DM1) (wz hd) s10 s11 t3 t4 t5 t6)
               F_ (wz (if r =? 0 then 0x786b4 else 0x78760)) fc None m1 (seg_rom asegs)
      /\ (r <> 0 -> a0 = wz r)
      /\ munch [(q - 224, q)] m0 m1 /\ wmono asegs m0 m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (q - 112)
      /\ rw_cells asegs m1 (q - 112) [CB 8 j0; C8 (wz TR); C8 (wz n); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 bp [C4 (wz hd)] /\ u64arr asegs m1 TR ws.

  #[using="L total DLO RD0 BUF TRW LEN LTR RNG QTR TRH ROOM_N MI0"] Lemma put_A : forall lo t0 t1 a2 a3 a4 a5 a6 a7,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 224 ->
    evt asegs (put_mid lo t0 t1)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz TR) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz depot_put_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo t0 t1 a2 a3 a4 a5 a6 a7 ST CLO LO. unfold depot_put_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof DLO as DL. unfold dl_ok in DL.
    pose proof (munch_refl [(q - 224, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM. pose proof MI0 as MI.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB. pose proof BUF as BUF1.
    pose proof (depot_hash_range tr) as HR.
    pose proof RD0 as RD. destruct RD as (TAB & NI & M1 & NR & FS & SA & SD & FF & RGH & T0 & TS & NB).
    pose proof (bkt_range h) as BR.
    destruct (tabrep_split m0 hs (bkt h) TAB BR) as [TB TX]. clear TAB TX FS FF.
    pose proof (head_of_bound hs (bkt h)) as HDB. unfold zlen in HDB, NB, ROOM_N.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 112%nat ST. rewrite !E in *.

    do 8 zstep.

    do 12 sstep.
    zstep. zstep.
    sstep. sstep.
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear. intros K0. rewrite ?unsigned_lit in K0 by lia. lia. }
    zstep.   rewrite Z.add_0_r, (STRW_merge.swrap32_small n) by lia.
    zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1 LTR. clear. intros. rewrite ?unsigned_lit in K1 by lia. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 QTR LO CLO ACR. clear. intros. rewrite ?unsigned_lit in K2 by lia. lia. }

    do 14 zstep.
    replace (Z.shiftr n 32) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    change 4294967295 with (Z.ones 32). rewrite !Z.land_ones by lia. rewrite !(Z.mod_small n (2^32)) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. replace (TR + n * 8) with (TR + 8 * n) by lia.
    replace (Z_to_bv 64 TR) with (Z_to_bv 64 (TR + 8 * Z.of_nat 0)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (hash_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc TR _ ws tr); try eassumption; try lia.
      { reflexivity. }
      cbn [firstn fold_left]. unfold mm_init. rewrite M64_eq. change (2^64) with 18446744073709551616.
      rewrite unsigned_lit; [reflexivity|].
      split; [apply Z.lxor_nonneg; split; intros; try lia; apply Z.mod_pos_bound; lia|].
      apply (PropExec.Z_lxor_range); [apply Z.mod_pos_bound; lia| lia]. }
    intros ms1 HP. destruct HP as (hv & x15 & x16 & -> & Hh). cbn beta in Hh.

    do 16 zstep.
    rewrite mm_fin_eq, Hh. change (mm_fin (fold_left mm_add tr (mm_init n))) with h.

    zstep. zstep.   rewrite (shl44_shr42 h) by lia.
    zstep.
    set (bpv := DT + 4 * bkt h) in *. assert (Hbp : bpv = DT + 4 * bkt h) by reflexivity. clearbody bpv.
    zstep.   rewrite (sx32_lit (head_of hs (bkt h))) by lia.
    do 7 zstep.
    change 2147483647 with (Z.ones 31). rewrite Z.land_ones by lia. rewrite (Z.mod_small (head_of hs (bkt h)) (2^31)) by lia.
    change (Z.ones 31) with 2147483647.
    replace (DT + 4194320) with DM1 by reflexivity. replace (DT + 4194312) with 5858336 by reflexivity.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (nodesrep_transport L m0 mm hs _ NR MU WM ltac:(intros i Hi; unfold zlen in Hi; cbn [disjoint_from]; lia)) as NR1 end.
    eapply evt_cut.
    { eapply (find_loop L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz h) _ _ _ _ _ _ _ _ _ _ F_ fc _ hs h DLO ltac:(apply unsigned_lit; lia) NR1
                ltac:(eassumption) RGH ltac:(unfold zlen; lia) (length hs) (length hs) (length hs)); [reflexivity| lia| lia|].
      rewrite firstn_all. reflexivity. }
    intros ms2 FP. change (find_fuel (S (length hs)) hs (length hs) (bkt h) h) with (dfind hs h) in FP.
    pose proof (dfind_bound hs h) as DB. subst bpv.
    destruct FP as [[R0 (x10 & x12 & ->)] | [R1 (x11 & ->)]].
    - apply evt_done. unfold put_mid. rewrite R0. cbn [Z.eqb].
      eexists _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [intros C; exfalso; exact (C eq_refl)|].
      repeat match goal with |- _ /\ _ => split end; try eassumption.
    - apply evt_done. unfold put_mid. replace (dfind hs h =? 0) with false by (symmetry; apply Z.eqb_neq; exact R1).
      eexists _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [intros _; reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try eassumption.
  Qed.
  #[using="ws tr DLO LEN LTR"] Lemma depot_apart_stack : forall lo', alloc_ceiling <= lo' -> depot_apart L [(lo', q)].
  Proof.
    intros lo' H. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof DLO as DL. unfold dl_ok in DL. unfold depot_apart. apply Forall_cons; [cbn; lia| apply Forall_nil].
  Qed.

  #[using="LTR"] Lemma sub_fp_stack_W : sub_fp [(q - 224, q)] W.
  Proof. unfold sub_fp. cbn [outside]. intros x Hx. tauto. Qed.

  #[using="DLO RD0 LEN LTR"] Lemma put_B : forall lo t0 t1 ms1, alloc_ceiling <= lo -> lo <= q - 224 -> dfind hs h <> 0 ->
    put_mid lo t0 t1 ms1 -> evt asegs (put_post lo) ms1.
  Proof.
    intros lo t0 t1 ms1 CLO LO R1 PM.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof DLO as DL. unfold dl_ok in DL. pose proof (bkt_range h) as BR. pose proof (depot_hash_range tr) as HR.
    destruct PM as (a0 & a1 & a2 & a5 & a6 & a7 & m1 & j0 & E & A0 & MU & WM & MI & ST & FR & TB & BUF1).
    cbn zeta in E. replace (dfind hs h =? 0) with false in E by (symmetry; apply Z.eqb_neq; exact R1). subst ms1.
    rewrite (A0 R1).
    do 11 zstep. zstep. replace (q - 112 + 112) with q by lia. zstep.
    release_frame FR ST q.
    apply evt_done. unfold put_post.
    eexists _, _, _, _, _, _, _, _, _, _, (dfind hs h), hs, total. split; [reflexivity|].
    split; [eapply munch_weaken; [apply sub_fp_stack_W| exact MU]|].
    split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [eapply RDEPOT_frame; [exact RD0| exact MU| exact WM| apply depot_apart_stack; lia]|].
    split; [exact BUF1|]. left. repeat split; reflexivity || exact R1.
  Qed.
End PUT.
