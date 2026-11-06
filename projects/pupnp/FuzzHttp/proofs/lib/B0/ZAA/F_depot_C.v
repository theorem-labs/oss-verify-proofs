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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import ADepot ATacA ACells F_imemcpy F_depot_H F_depot_L F_depot_S F_depot.
Import ListNotations.
Open Scope Z_scope.

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

  Notation put_post := (put_post L ra gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc q TR total m0 hs ws tr).
  Notation put_mid := (put_mid ra gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc q TR m0 hs ws tr).

  #[using="DLO RD0 BUF TRW LEN LTR QTR TRH QAL ROOM_N ROOM_F ROOM_T"] Lemma put_C : forall lo t0 t1 ms1, alloc_ceiling <= lo -> lo <= q - 224 -> dfind hs h = 0 ->
    put_mid lo t0 t1 ms1 -> evt asegs (put_post lo) ms1.
  Proof.
    intros lo t0 t1 ms1 CLO LO R0 PM.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof DLO as DL. unfold dl_ok in DL. pose proof (bkt_range h) as BR. pose proof (depot_hash_range tr) as HR.
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB.
    destruct PM as (a0 & a1 & a2 & a5 & a6 & a7 & m1 & j0 & E & A0 & MU & WM & MI & ST & FR & TB & BUF1).
    cbn zeta in E. rewrite R0 in E. cbn [Z.eqb] in E. subst ms1. clear A0.
    pose proof RD0 as RD. destruct RD as (TAB & NI & M1 & NR & FS & SA & SD & FF & RGH & T0 & TS & NB).
    destruct (tabrep_split m0 hs (bkt h) TAB BR) as [_ TX]. clear TAB.
    pose proof (head_of_bound hs (bkt h)) as HDB. unfold zlen in HDB, NB. pose proof ROOM_N as RN. unfold zlen in RN.
    assert (ZB : 0 <= zlen hs /\ 16 * (zlen hs + 2) <= 2^20) by (unfold zlen in *; lia).

    assert (DJ : forall A k, A + k <= alloc_ceiling -> disjoint_from [(q - 224, q)] A k) by (intros A k HA; cbn; lia).
    pose proof (rw_cells_transport asegs _ m0 m1 _ _ NI MU WM ltac:(apply DJ; cbn; lia)) as NI1.
    pose proof (rw_cells_transport asegs _ m0 m1 _ _ M1 MU WM ltac:(apply DJ; cbn; lia)) as M11.
    pose proof (rw_cells_transport asegs _ m0 m1 _ _ SA MU WM ltac:(apply DJ; cbn; lia)) as SA1.
    pose proof (rw_cells_transport asegs _ m0 m1 _ _ SD MU WM ltac:(apply DJ; cbn; lia)) as SD1.
    clear NI M1 SA SD.
    destruct FF as [jf FF0]. match type of FF0 with ?P => change P with (id P) in FF0 end.
    destruct FS as [jn FS0].
    apply (rw_cells_split_CB asegs m0 _ [] _ jn [] [8%nat; 4%nat; 4%nat; (Z.to_nat (2^20 - 16 * (zlen hs + 1)) - 16)%nat]) in FS0; [cbn [mk_CB_cells app] in FS0| cbn [sum_nat]; unfold zlen; lia].
    split_chunk FS0 3%nat NDC0 FST0.
    match type of FST0 with rw_cells _ _ ?a _ => replace a with (DN0 L + 16 * (zlen hs + 2)) in FST0 by lia end.
    replace (Z.to_nat (2^20 - 16 * (zlen hs + 1)) - 16)%nat with (Z.to_nat (2^20 - 16 * (zlen hs + 2))) in FST0 by lia.
    match type of FST0 with ?P => change P with (id P) in FST0 end.
    pose proof (rw_cells_transport asegs _ m0 m1 _ _ NDC0 MU WM ltac:(apply DJ; cbn; unfold zlen; lia)) as NDC. clear NDC0.

    set (bpv := DT + 4 * bkt h) in *. assert (Hbp : bpv = DT + 4 * bkt h) by reflexivity. clearbody bpv.
    apply (munch_weaken _ [(q - 224, q); (bpv, bpv + 4); (DNI, DNI + 4)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto].
    zstep.
    zstep.
    call lock_spec.
    all: side (try (first [ eassumption | unfold zlen in *; lia ])).
    zstep.
    zstep. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear. intros K0. lia. }
    zstep. zstep.   replace (DT + 4194304) with DNI by reflexivity.
    zstep.
    amo_step.
    rewrite (amo_addw_bytes_lit (zlen hs) 1) by (unfold zlen; lia). mem_after_store.
    rewrite (sx32_lit (zlen hs)) by (unfold zlen; lia).
    zstep.   rewrite (STRW_merge.swrap32_small (zlen hs + 1)) by lia.
    zstep. zstep.   rewrite (Z.mod_small (zlen hs + 1) 4294967296) by lia.
    zstep. if_cases K1; zify_cond K1. { exfalso. revert K1 RN. clear. unfold zlen. intros. rewrite ?unsigned_lit in K1 by lia. lia. }
    zstep.
    zstep.   replace (Z.shiftr (zlen hs + 1) 16) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; unfold zlen in *; lia).
    zstep. zstep.   change (Z.shiftl 0 3) with 0. replace (DM1 + 0) with DM1 by reflexivity.
    zstep.
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 DL. clear. intros. rewrite ?unsigned_lit in K2 by lia. lia. }
    zstep.   change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small (zlen hs + 1) (2^16)) by (unfold zlen in *; lia).
    zstep.   rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    zstep.   replace (DN0 L + (zlen hs + 1) * 16) with (DN0 L + 16 * (zlen hs + 1)) by lia.
    set (ndv := DN0 L + 16 * (zlen hs + 1)) in *. assert (Hnd : ndv = DN0 L + 16 * (zlen hs + 1)) by reflexivity. clearbody ndv.
    zstep. zstep. zstep. zstep.
    replace (q - 112 + 8) with (q - 104) by lia.
    zstep.

    unfold id in FF0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (rw_cells_transport asegs _ m0 mm _ _ FF0 MU WM ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as FF1 end.
    clear FF0.
    split_chunk FR 1%nat F0 F1. split_chunk F1 2%nat FA F2.
    match type of FA with rw_cells _ _ ?a _ => replace a with (q - 104) in FA by lia end.
    match type of F2 with rw_cells _ _ ?a _ => replace a with (q - 88) in F2 by lia end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (rw_cells_C8_C4C4 mm (q - 104) [C8 (wz TR)] n []) in FA; [cbn [app] in FA| lia] end.
    apply (munch_weaken _ [(q - 224, q); (bpv, bpv + 4); (DNI, DNI + 4); (ndv, ndv + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                            (SS0 L + 8 * total, SS0 L + 8 * total + 8 + 8 * n)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto].
    call (nstore_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (wz h) (q - 112) (SS0 L) total (q - 104) TR ndv (SWIN L - 8 * total) _ ws tr lo).
    all: side (try (first [ eassumption | unfold zlen in *; lia ])).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : rw_cells asegs mm (SS0 L + 8 * (total + n + 1)) _ |- _ =>
        rename H into FFN; match type of FFN with ?P => change P with (id P) in FFN end end;
      pose proof (munch_refl [(ndv + 8, ndv + 12); (bpv, bpv + 4)] mm) as MUr; pose proof (wmono_refl asegs mm) as WMr end.
    sstep.
    zstep. zstep.
    sstep.
    zstep. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3. clear. intros K3. rewrite ?unsigned_lit in K3 by lia. lia. }

    match goal with H : rw_cells asegs ?mm (q - 104) _ |- _ =>
      apply (rw_cells_C4C4_C8 mm (q - 104) [C8 (wz TR)] n []) in H; [cbn [app] in H| lia]; join_chunks H F2 F1; join_chunks F0 F1 FR end.
    do 11 zstep. zstep. replace (q - 112 + 112) with q by lia. zstep.
    match goal with H : stk asegs _ lo _ |- _ => release_frame FR H q end.

    unfold id in FST0, FFN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      pose proof (rw_cells_transport asegs _ _ mf _ _ FFN MUr WMr ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as FF2;
      pose proof (rw_cells_transport asegs _ m0 mf _ _ FST0 MU WM ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; unfold zlen in *; lia)) as FS2;
      pose proof (tabrep_x_transport m0 mf hs (bkt h) _ TX MU WM ltac:(intros b Hb Hx; cbn [disjoint_from]; unfold zlen in *; lia)) as TX2;
      pose proof (nodesrep_transport L m0 mf hs _ NR MU WM ltac:(intros i Hi; unfold zlen in *; cbn [disjoint_from]; lia)) as NR2
    end.
    clear FST0 FFN MUr WMr.
    subst bpv ndv.
    apply evt_done. unfold F_depot.put_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      eexists _, _, _, _, _, _, _, _, _, mf, (zlen hs + 1), (hs ++ [h]), (total + n + 1) end.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split.
    { unfold RDEPOT. rewrite !zlen_snoc.
      split. { eapply (tabrep_join _ hs (hs ++ [h]) (bkt h) (zlen hs + 1) TX2 BR); [eassumption|].
               intros b Hb. rewrite head_of_snoc, (Z.eqb_sym (bkt h) b). reflexivity. }
      split; [assumption|]. split; [assumption|].
      split. { eapply nodesrep_snoc; [exact NR2| eassumption]. }
      split. { eexists. replace (zlen hs + 1 + 1) with (zlen hs + 2) by lia. exact FS2. }
      split; [assumption|]. split; [assumption|].
      split. { eexists. replace (Z.to_nat (SWIN L - 8 * (total + n + 1))) with (Z.to_nat (SWIN L - 8 * total - 8 - 8 * n)) by lia. exact FF2. }
      split. { apply Forall_app. split; [exact RGH| apply Forall_cons; [exact HR| apply Forall_nil]]. }
      unfold zlen in *. lia. }
    split; [assumption|]. right. repeat split; reflexivity || exact R0.
  Qed.

  #[using="DLO RD0 BUF TRW LEN LTR RNG QTR TRH QAL ROOM_N ROOM_F ROOM_T MI0"] Theorem put_spec : forall lo t0 t1 a2 a3 a4 a5 a6 a7,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 224 ->
    evt asegs (put_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz TR) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz depot_put_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo t0 t1 a2 a3 a4 a5 a6 a7 ST CLO LO.
    eapply evt_cut; [eapply (put_A L); eassumption|].
    intros ms1 PM. destruct (Z.eq_dec (dfind hs h) 0) as [R0|R1].
    - eapply put_C; eassumption.
    - eapply put_B; eassumption.
  Qed.
End PUT.
