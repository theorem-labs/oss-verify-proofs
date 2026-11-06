(* fuzz_alloc_fail 0x81bc0 (alloc.c:138-141): g_fail_at = g_count + k, saturated to SIZE_MAX on carry
   (add; sltu; neg; or; sd). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_alloc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the saturating add the three instructions after the load compute *)
Lemma lor_ones64 : forall s, 0 <= s < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) s = 2 ^ 64 - 1.
Proof.
intros s Hs. replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.testbit_ones by lia.
replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.ltb_spec i 64) as [Hlt|Hge]; [reflexivity|].
rewrite Bool.orb_false_l. apply Z.bits_above_log2; [lia|].
destruct (Z.eq_dec s 0) as [->|Hn]; [cbn; lia|].
pose proof (Z.log2_lt_pow2 s 64 ltac:(lia)) as [Hl _]. specialize (Hl ltac:(lia)). lia.
Qed.

(* the word fuzz_alloc_fail stores (MEASURED: vm_compute of the run's chunk at g_fail_at; a0 = k is atom 10,
   g_count is atom 32), named so that no tactic has to compute it under an evar *)
Definition fail_e : sv :=
  SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 0) (SOff 32 0)) (SOff 32 0)))
              (SAlu ALU_ADD (SOff 10 0) (SOff 32 0)).

Lemma fail_value : forall (rho : nat -> Z) k cnt,
  rho 10%nat = k -> rho 32%nat = cnt -> 0 <= k < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
  AF0x.zev rho fail_e = if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ.
Proof.
intros rho k cnt Hk Hc Hkr Hcr. unfold fail_e. cbn [AF0x.zev zalu_raw]. rewrite Hk, Hc. unfold zcanon, M64.
rewrite !Z.add_0_r. rewrite (Z.mod_small k) by exact Hkr. rewrite (Z.mod_small cnt) by exact Hcr.
rewrite ?Zmod_0_l. unfold SIZE_MAXZ.
destruct (Z.ltb_spec (cnt + k) (2 ^ 64)) as [Hlt|Hge].
- rewrite (Z.mod_small (k + cnt)) by lia.
  replace (k + cnt <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota.
  rewrite ?Zmod_0_l, ?Z.sub_0_r, ?Zmod_0_l, Z.lor_0_l.
  rewrite (Z.mod_small (k + cnt)) by lia. lia.
- assert (Hm : (k + cnt) mod 2 ^ 64 = k + cnt - 2 ^ 64).
  { symmetry. apply (Z.mod_unique (k + cnt) (2 ^ 64) 1); lia. }
  rewrite Hm.
  replace (k + cnt - 2 ^ 64 <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). cbv beta iota.
  rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
  replace ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1)
    by (first [apply (Z.mod_unique (0 - 1) (2 ^ 64) (-1)) | symmetry; apply (Z.mod_unique (0 - 1) (2 ^ 64) (-1))]; lia).
  rewrite (lor_ones64 (k + cnt - 2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.

Definition ss_fl : sstate :=
  mkSS A_fuzz_alloc_fail sr_atoms [fm_rcell G_COUNT 32; fm_wcell G_FAIL 33] None (mkFacts [] [] []).

Theorem fuzz_alloc_fail_holds : fuzz_alloc_fail_spec tfibsegs B.
Proof.
intros ly S W regs mem md ch live peak cnt fail k HPRE HG G10 Hk.
pose proof HPRE as (HAN & _).
pose proof HAN as (HAR & Hra & _ & _ & _ & Hstk & HpresE & _). unfold YK0s.ret_ok in Hra.
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof HG as (GL & GP & GC & GF & Hlp & Hp64 & Hc64 & Hf64).
pose proof fma_wx as Hwx.
assert (HS : st_ok tfibsegs (Ereg regs [w64 cnt; w64 fail]) ss_fl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_alloc_fail) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_fm_rcell _ _ G_COUNT 32 cnt); [exact GC | | lia | unfold G_COUNT; lia | unfold G_COUNT; lia].
      exact (ew_Ereg_extra regs [w64 cnt; w64 fail] 0).
    + apply (region_ok_fm_wcell _ _ G_FAIL 33 fail); [exact GF | | lia | unfold G_FAIL; lia | unfold G_FAIL; lia].
      exact (ew_Ereg_extra regs [w64 cnt; w64 fail] 1).
  - cbn. repeat split; try exact I; unfold extent_disjoint, fm_rcell, fm_wcell, G_COUNT, G_FAIL;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia.
  - exact I. }
unfold cfg_at. change (w64 A_fuzz_alloc_fail) with (Z_to_bv 64 A_fuzz_alloc_fail).
remember (Ereg regs [w64 cnt; w64 fail]) as E eqn:HE.
srr_run_with tbl_fma_ok HS.
eapply (SRr_ret_at tfibsegs tbl_fma tbl_fma_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 cnt; w64 fail] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = w64 k)
  by (rewrite HE, (ew_Ereg_nat regs [w64 cnt; w64 fail] 10 10%bv eq_refl); exact G10).
assert (E32 : ew E 32 = w64 cnt) by (rewrite HE; exact (ew_Ereg_extra regs [w64 cnt; w64 fail] 0)).
rreg HS (1%bv : bv 5) R1.
set (res := if cnt + k <? 2 ^ 64 then cnt + k else SIZE_MAXZ) in *.
assert (Hres : 0 <= res < 2 ^ 64).
{ unfold res, SIZE_MAXZ. destruct (Z.ltb_spec (cnt + k) (2 ^ 64)); lia. }
assert (WIN : forall a, in_wrange E (ss_mem ss_fl) a -> G_FAIL <= a < G_FAIL + 8).
{ intros a (r & Hin & Hw). cbn [ss_fl ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [fm_rcell fm_wcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
assert (RAW : forall x : word, ~ (G_FAIL <= bv_unsigned x < G_FAIL + 8) -> ms_mem ms x = mem x).
{ intros x Hx. apply HF. intros Hin. exact (Hx (WIN _ Hin)). }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (G_FAIL <= a < G_FAIL + 8) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hc. apply aview_eq_of. unfold mrestrict. rewrite RAW; [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hc. }
assert (Uk : bv_unsigned (ew E 10) = k) by (rewrite E10; unfold YG0d.w64; apply unsigned_lit_small; lia).
assert (Uc : bv_unsigned (ew E 32) = cnt) by (rewrite E32; unfold YG0d.w64; apply unsigned_lit_small; lia).
(* the stored word, as the run computes it (MEASURED by vm_compute of the run): OR (SUB 0 (SLTU (k + cnt) cnt)) (k + cnt) *)
assert (VAL : forall e, AF0x.svpure e = true ->
  AF0x.zev (AF0x.rho_of E) e = res -> sv_denot E e = Z_to_bv 64 res).
{ intros e Hp Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E e)) with (U E e).
  rewrite (AF0x.U_zev E e Hp), Hz. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. symmetry. apply Z.mod_small. exact Hres. }
assert (VF : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) G_FAIL 8 res).
{ assert (Hk' : 0 <= k < 2 ^ 64) by lia. assert (Hc' : 0 <= cnt < 2 ^ 64) by lia.
  apply (val_mem_of_chunk8 E _ _ 1%nat G_FAIL fail_e res (st_ok_mem_ok E _ (w_H W) ms HS));
  [ vm_compute; reflexivity | | exact Hres ].
  apply VAL; [vm_compute; reflexivity|].
  exact (fail_value (AF0x.rho_of E) k cnt Uk Uc Hk' Hc'). }
assert (HVIS : forall i, 0 <= i < 8 -> aview tfibsegs (w_H W) (ms_mem ms) (G_FAIL + i) <> None).
{ intros i Hi. exact (aview_some_of_val_mem (w_H W) (ms_mem ms) G_FAIL 8 res i VF ltac:(cbn; lia)). }
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms) md).
{ apply (AR_write_static B HB ly S W mem md (ms_mem ms) G_FAIL HAR
    ltac:(vm_compute; tauto) RAW HVIS). }
unfold fpost, apost_base.
exists ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat2 md).
split; [rewrite R1, E1, Hra; reflexivity|].
split.
{ apply (ajournal_materialize tfibsegs B (AR_laws_ok tfibsegs B) fma_segs_low).
  apply (ajournal_pstat1 B STK_fuzz_alloc ly S W regs mem md ch (ms_mem ms) G_FAIL HAN
    ltac:(vm_compute; tauto) HAR2).
  - intros a Ha _ Hc. exact (AV a Ha Hc).
  - intros a Ha. destruct (HpresE a Ha) as [Hh [b Hb]].
    split; [exact Hh|]. exists b. rewrite RAW; [exact Hb|].
    rewrite unsigned_lit_small by (unfold STK_fuzz_alloc in *; lia). unfold G_FAIL, STK_fuzz_alloc in *. lia. }
split.
{ eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity]. }
split; [reflexivity|].
split; [| split; [| split; [| split; [exact VF | lia]]]].
- eapply val_mem_kept; [exact GL|]. intros i Hi. apply AV; unfold G_LIVE, G_FAIL; cbn in Hi; lia.
- eapply val_mem_kept; [exact GP|]. intros i Hi. apply AV; unfold G_PEAK, G_FAIL; cbn in Hi; lia.
- eapply val_mem_kept; [exact GC|]. intros i Hi. apply AV; unfold G_COUNT, G_FAIL; cbn in Hi; lia.
Qed.

End c.
