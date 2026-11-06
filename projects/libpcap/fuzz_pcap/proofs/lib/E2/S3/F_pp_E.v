(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pp_ctx. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pp_ctx.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
#[local] Ltac2 Set StepFast.sf_proj_inert := Ltac2.Init.true.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac bd_F := try lstep; bfalse.
Local Ltac bd_T := try lstep; btrue.
Local Ltac gsplit_FF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_FT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac gsplit_TF x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_F; cbn [orb andb negb]].
Local Ltac gsplit_TT x k := let C := fresh "Hc" in destruct (Z.ltb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb]; epilog | bd_T; cbn [orb andb negb]].
Local Ltac esplit_FF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_FT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_F; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Local Ltac esplit_TF x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_F; cbn [orb andb negb]].
Local Ltac esplit_TT x k := let C := fresh "He" in destruct (Z.eqb_spec x k) as [C|C]; [bd_T; cbn [orb andb negb] | bd_T; cbn [orb andb negb]].
Lemma swap_nflog_tlvs_S : forall f cap len p d,
  swap_nflog_tlvs (S f) cap len p d =
  (if cap <? 4 then d else
  let d2 := swap_field 2 p (swap_field 2 (p + 2) d) in
  let size := get_le16 d2 p in
  let size' := if size mod 4 =? 0 then size else size + (4 - size mod 4) in
  if size' <? 4 then d2 else if (cap <? size') || (len <? size') then d2
  else swap_nflog_tlvs f (cap - size') (len - size') (p + size') d2)%Z.
Proof. reflexivity. Qed.
Lemma swap_nflog_tlvs_exit : forall f cap len p d, (cap < 4)%Z -> swap_nflog_tlvs f cap len p d = d.
Proof. intros [|f] cap len p d H; [reflexivity|]. rewrite swap_nflog_tlvs_S. replace (cap <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Ltac close_inv := unfold ppinv; repeat match goal with |- _ /\ _ => split end; first [hyp_by_addr | assumption | reflexivity].
Ltac wordeq := fastfirst (first [ noevar_assumption | reflexivity | (f_equal; lia) | (f_equal; rewrite ?swrap32_small by lia; lia) | (do 2 f_equal; lia)
                     | apply sx32_as_swrap | (symmetry; apply sx32_as_swrap) ]).
Ltac rf_norm := rewrite ?sx32_as_swrap, ?unsigned_RF, ?swrap32_add_mod64_l, ?swrap32_add_mod64_r, ?swrap32_sub_mod64_l, ?Z.add_0_r.
(* [comment removed for export] *)
Ltac nf_exit := run; bdecide; epilog.
Local Ltac nf_exit__c1 := run; bd_T; epilog.
Local Ltac nf_exit__c2 := run; bd_T; epilog.
Local Ltac nf_exit__c3 := run; bd_T; epilog.
Local Ltac nf_exit__c4 := run; bd_T; epilog.

Definition nflog_loop__stmt : Prop := forall c, ppwf c -> forall (f : nat) (capc lenc p : Z),
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  (4 * Z.of_nat f >= capc + 4)%Z -> (4 <= capc)%Z -> (p + capc = c_caplen c)%Z -> (4 <= p)%Z -> (0 <= lenc < 2^32)%Z ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  a1 = Z_to_bv 64 capc -> a5 = Z_to_bv 64 (c_DA c + p) -> a6 = Z_to_bv 64 (bv_swrap 32 lenc) ->
  a4 = Z_to_bv 64 4 -> a7 = Z_to_bv 64 65532 -> t0 = Z_to_bv 64 3 ->
  evt ssegs (ppost c (c_len0 c) (swap_nflog_tlvs f capc lenc p d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16280) (c_fc c) None m (seg_rom ssegs)).
Section Sz3.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_loop__stmt "vhk" @c).
#[using="Type"] Lemma nflog_loop__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_loop__stmt "vhk").
Proof.
  intros f WF.
 induction f as [|f IH]; intros capc lenc p; intros until d; intros I FU C4p PC P4 LR -> -> -> -> -> -> -> -> ->.
  { exfalso. lia. }
  pose proof WF as WF'. pp_init WF I.
  rewrite swap_nflog_tlvs_S. replace (capc <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv zeta. simpl_if.
  set (d2 := swap_field 2 p (swap_field 2 (p + 2) d)).
  set (size := get_le16 d2 p).
  set (size' := if (size mod 4 =? 0)%Z then size else (size + (4 - size mod 4))%Z).
  rd2 (p + 2)%Z. rd2 p. run.
  name2 p. name2 (p + 2)%Z.
  lazymatch goal with EWa : zslice p 2 d = [?y0; ?y1], EWb : zslice (p + 2) 2 d = [?y2; ?y3] |- _ =>
    sh_lanes p [y1; y0]; sh_lanes (p + 2)%Z [y3; y2];
    (* [comment removed for export] *)
    let E := fresh "E" in
    assert (E : buf_write_at (p + 2) [y3; y2] (buf_write_at p [y1; y0] d) = d2)
      by (subst d2; apply (tlv_pair p (p + 2) d y0 y1 y2 y3); [lia | lia | reflexivity | exact EWa | exact EWb]);
    assert (SZ : size = (y1 + 256 * y0)%Z)
      by (subst size; rewrite <- E; apply (tlv_pair_size p (p + 2) d y0 y1 y2 y3); lia);
    rewrite E in *; clear E; clearbody d2;
    (* [comment removed for export] *)
    rewrite (get_le16_of_slice _ _ _ _ EWa); rewrite swap16_val by lia;
    (* [comment removed for export] *)
    replace size' with (if ((y1 + 256 * y0) mod 4 =? 0)%Z then (y1 + 256 * y0)%Z else (y1 + 256 * y0 + (4 - (y1 + 256 * y0) mod 4))%Z)
      by (subst size' size; rewrite SZ; reflexivity);
    clear size' size SZ;
    set (sw := (y1 + 256 * y0)%Z) in *;
    assert (SW : (0 <= sw < 65536)%Z) by lia;
    rewrite land_3 by lia;
    replace ((sw + 65536 * y1) mod 4)%Z with (sw mod 4)%Z by zlia
  end.
  (* [comment removed for export] *)
  assert (CONT : forall (t1' t2' t3' : word) (sz : Z), (0 <= sz < 2^32)%Z -> t1' = Z_to_bv 64 sz ->
    evt ssegs (ppost c (c_len0 c)
                (if sz <? 4 then d2 else if (capc <? sz) || (lenc <? sz) then d2
                 else swap_nflog_tlvs f (capc - sz) (lenc - sz) (p + sz) d2))
      (MS (mkR ra (SPM c) (c_gp c) (c_tp c) (Z_to_bv 64 3) t1' t2' s0 s1 (Z_to_bv 64 239) (Z_to_bv 64 capc)
               (Z_to_bv 64 (c_HA c)) (Z_to_bv 64 (c_DA c)) (Z_to_bv 64 4) (Z_to_bv 64 (c_DA c + p))
               (Z_to_bv 64 (bv_swrap 32 lenc)) (Z_to_bv 64 65532) s2
               (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3' t4 t5 t6)
          (c_F c) (Z_to_bv 64 0x162c4) (c_fc c) None m (seg_rom ssegs))).
  { intros t1' t2' t3' sz SZR ->.
    run. destruct (Z.ltb_spec sz 4) as [S4|S4]. { bd_T. nf_exit__c1. } bd_F.
    run. destruct (Z.ltb_spec capc sz) as [S5|S5]. { bd_T. cbn [orb]. nf_exit__c2. } bd_F. cbn [orb].
    run. destruct (Z.ltb_spec lenc sz) as [S6|S6]. { bd_T. nf_exit__c3. } bd_F.
    run. rf_norm.
    destruct (Z.ltb_spec 3 (capc - sz)) as [S7|S7]; cycle 1.
    { bd_F. rewrite swap_nflog_tlvs_exit by lia. nf_exit__c4. }
    bd_T. eapply (IH (capc - sz)%Z (lenc - sz)%Z (p + sz)%Z); fastfirst (first [ noevar_assumption |close_inv | wordeq | lia]). }
  destruct (Z.eqb_spec (sw mod 4) 0) as [M0|M0]; simpl_if.
  - bd_T. do 2 lstep.
    match goal with |- context [((sw + 65536 * ?y) mod 65536)%Z] =>
      replace ((sw + 65536 * y) mod 65536)%Z with sw by zlia end.
    eapply (CONT _ _ _ sw); [lia | reflexivity].
  - bd_F. lstep. rewrite land_65532 by lia.
    match goal with |- context [((sw + 65536 * ?y) mod 65536 - (sw + 65536 * ?y) mod 4)%Z] =>
      replace ((sw + 65536 * y) mod 65536 - (sw + 65536 * y) mod 4)%Z with (sw - sw mod 4)%Z by zlia end.
    do 2 lstep.
    eapply (CONT _ _ _ (sw + (4 - sw mod 4))%Z); [zlia | wordeq].
Qed.
End Sz3.
Lemma nflog_loop : ltac:(let t := eval cbv delta [nflog_loop__stmt] in nflog_loop__stmt in exact t).
Proof. intros c WF f. ltac2:(SecDiet.SzSec.closeP 'nflog_loop__body "vhk"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nflog_spec__stmt : Prop := forall c, ppwf c ->
  forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m d,
  ppinv c m d (c_len0 c) ->
  a0 = Z_to_bv 64 239 -> a2 = Z_to_bv 64 (c_HA c) -> a3 = Z_to_bv 64 (c_DA c) ->
  evt ssegs (ppost c (c_len0 c) (swap_nflog_header (mkHdr 0 0 (c_caplen c) (c_len0 c)) d))
    (MS (mkR ra (SPM c) (c_gp c) (c_tp c) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (c_s3 c) (c_s4 c) (c_s5 c) (c_s6 c) (c_s7 c) (c_s8 c) (c_s9 c) (c_s10 c) (c_s11 c) t3 t4 t5 t6)
        (c_F c) (Z_to_bv 64 0x16244) (c_fc c) None m (seg_rom ssegs)).
Section Sz4.
Variables c : ltac2:(SecDiet.SzSec.tyM 'nflog_spec__stmt "v" @c).
#[using="Type"] Lemma nflog_spec__body : ltac2:(SecDiet.SzSec.bodyP 'nflog_spec__stmt "v").
Proof.
  intros WF; intros until d; intros I -> -> ->.
 pose proof WF as WF'. pp_init WF I.
  unfold swap_nflog_header. cbn [h_caplen h_len].
  run. gsplit_TF (c_caplen c) 4%Z.
  run. gsplit_TF (c_len0 c) 4%Z.
  rd1 1%Z. run.
  destruct (Z.eqb_spec (get_u8 d 1) 0) as [V0|V0]; cycle 1.
  { bd_T. cbn [negb]. epilog. }
  bd_F. cbn [negb]. run. rf_norm. rewrite (swrap32_small (c_caplen c + -4)) by lia.
  destruct (Z.ltb_spec (c_caplen c - 4) 4) as [C8'|C8'].
  { bd_T. rewrite swap_nflog_tlvs_exit by lia. epilog. }
  bd_F. run. rf_norm.
  eapply (nflog_loop c WF' (Z.to_nat (c_caplen c / 4 + 1)) (c_caplen c - 4)%Z (c_len0 c - 4)%Z 4%Z);
    fastfirst (first [ noevar_assumption |close_inv | wordeq | lia]).
Qed.
End Sz4.
Lemma nflog_spec : ltac:(let t := eval cbv delta [nflog_spec__stmt] in nflog_spec__stmt in exact t).
Proof. intros c. ltac2:(SecDiet.SzSec.closeP 'nflog_spec__body "v"). Qed.
