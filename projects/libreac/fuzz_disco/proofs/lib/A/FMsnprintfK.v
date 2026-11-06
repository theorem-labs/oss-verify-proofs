(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfK.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan (module paths). kcall generalizes A/AE3h.v vf_icpt_xcall (callee post handed in, regions after the
   stack region constrained by what they must avoid); kentry, kenv, st_ok_pc_mem_out and kstore0 are new. *)
(* Kit for the snprintf walks in the donor's symbolic engine: a call step that resumes a symbolic walk after a callee
   whose effect is given as an SRr fact (the donor's A/AE3h.v vf_icpt_xcall, with the callee's post handed in instead
   of fixed, and the regions after the stack region constrained by what they must avoid instead of by their base). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AE34 AF0l AE3e AE3f AE3g AE6g AE39 AE2p AE3i AF0m AE22 AF0x AE20 AE2y AE7f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The state after a call returns to ra: caller-saved registers havoc'd from atom k on, the stack region keeps its
   chunks at offsets >= osp (the caller's frame) that miss the window [xlo, xhi) the callee writes. *)
Definition kafter (k : nat) (ss : sstate) (ra osp xlo xhi : Z) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS ra (sr_sets (ss_regs ss) (junk_upd k CLOB))
(YP09.mkRegion (YP09.r_base r0) (YP09.r_lo r0) (YP09.r_hi r0) (YP09.r_wlo r0) (YP09.r_whi r0)
(List.filter (fun c => (osp <=? YP09.c_off c) && chunk_out xlo xhi c) (YP09.r_chunks r0))
:: rest)
None (ss_facts ss)
| [] => ss
end.
Lemma kcall : forall (W : world tfibsegs) E ss ms md (sp0 K : Z) r0 rest k ra osp xlo xhi (BAND : Z) (XW : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Model -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> bv_unsigned (ew E 2) = sp0 ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - K -> YP09.r_hi r0 = 0 ->
- K <= YP09.r_wlo r0 -> YP09.r_whi r0 <= 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
no_cdata (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
mem_atoms_lt k (ss_mem (kafter k ss ra osp xlo xhi)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
0 <= BAND -> - K <= osp - BAND -> osp <= 0 -> 0 <= sp0 - K -> sp0 <= 2 ^ 63 ->
(forall a, XW a -> sp0 - K <= a < sp0 -> sp0 + xlo <= a < sp0 + xhi) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
0 <= a < 2 ^ 64 /\ ~ (sp0 + osp - BAND <= a < sp0 + osp) /\ ~ XW a) ->
(forall r a, In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, sp0 - K <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
SRr tfibsegs W (cfg_at tfibsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) md)
(fun W' c' => W' = W /\ exists regs2 mem2 md2,
c' = cfg_at tfibsegs ra regs2 mem2 md2 /\
aregs_preserved (ms_regs ms) regs2 /\ same_but_materialized md md2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - BAND <= a < sp0 + osp) -> ~ XW a ->
aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) /\ Q regs2 mem2 md2) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (kafter k ss ra osp xlo xhi) (restrict (w_H W) ms2) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - BAND <= a < sp0 + osp) -> ~ XW a ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a) /\
Q (ms_regs ms2) (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
Proof.
intros W E ss ms md sp0 K r0 rest k ra osp xlo xhi BAND XW Q HS Hrv Usp Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 Hat Hwf2 Hnc2 Hma2 Hci0 HB0 HKB Hosp Hsp0 Hsp63 HXWs Hrest HrestW Hpres HC.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
rewrite Hshape.
eapply SRr_mono; [unfold cfg_at in HC; exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HP & Hsbm & Hfr & Hpres2 & HQ).
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [unfold cfg_at, w64; rewrite <- Hsbm'; reflexivity|].
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0.
unfold kafter in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [exact HP | split; [|split; [exact Hpres2 | rewrite <- Hsbm'; exact HQ]]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (ss_pc ss)) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia | lia |].
intros Hx. pose proof (HXWs _ Hx ltac:(lia)) as Hxw.
apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. destruct (Hrest r a Hr Ha) as (Hr64 & Hb & Hx). apply Hfr; assumption.
++ intros a Ha _. apply apresent_writable. apply Hpres2. exact (HrestW r a Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- intros a Hr Hb Hx. apply Hfr; assumption.
Qed.
(* st_ok of an entry state under any environment (YI04.v entry_st_ok_full fixes the env to Ereg regs extra). *)
Lemma kentry : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok tfibsegs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G ->
st_ok tfibsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG].
split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
(* An environment whose atom 2 is a chosen value (the walk's frame base) and whose other atoms are the registers and
   the extra values, as Ereg. *)
Definition kenv (regs : bvmap 5 word) (sp0 : Z) (extra : list word) : env :=
mkEnv (fun i => if Nat.eqb i 2 then Z_to_bv 64 sp0 else ew (Ereg regs extra) i) (fun _ => []).
Lemma kenv_2 : forall regs sp0 extra, ew (kenv regs sp0 extra) 2 = Z_to_bv 64 sp0.
Proof. intros. reflexivity. Qed.
Lemma kenv_reg : forall regs sp0 extra i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r ->
ew (kenv regs sp0 extra) i = getr regs r.
Proof.
intros regs sp0 extra i r Hi Hr. unfold kenv. cbn [ew]. destruct (Nat.eqb_spec i 2); [lia|].
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma kenv_x : forall regs sp0 extra j, ew (kenv regs sp0 extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs sp0 extra j. unfold kenv. cbn [ew]. destruct (Nat.eqb_spec (32 + j) 2); [lia|].
apply ew_Ereg_extra.
Qed.
(* region_ok under the same environment when the bytes of the region's extent do not change (the proof of YN0g.v
   region_ok_transport). *)
Lemma kregion_transport : forall E m m' r,
region_ok tfibsegs E m r -> region_wf r = true ->
(forall x, base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
(forall x, base_val E (YP09.r_base r) + YP09.r_wlo r <= x < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs m x -> writable_at tfibsegs m' x) ->
region_ok tfibsegs E m' r.
Proof.
intros E m m' r (H1 & H2 & H3 & H4) Hwf Hrd Hwr.
apply region_wf_facts in Hwf as (_ & _ & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply Hwr; [lia|]. apply H3. exact Ho.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
rewrite Hrd by lia. exact Hb2.
Qed.
(* st_ok kept when the pc moves and the memory changes only outside every region of the symbolic state. *)
Lemma st_ok_pc_mem_out : forall E ss regs pc pc' (m m' : word -> option byte),
st_ok tfibsegs E ss (mkst regs pc m (seg_rom tfibsegs)) ->
(forall r x, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
(forall r x, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_wlo r <= x < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs m x -> writable_at tfibsegs m' x) ->
st_ok tfibsegs E (set_regs_pc ss [] pc') (mkst regs (Z_to_bv 64 pc') m' (seg_rom tfibsegs)).
Proof.
intros E ss regs pc pc' m m' HS Hm Hw.
destruct HS as (H1 & _ & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9).
unfold st_ok, set_regs_pc. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts sr_sets] in *.
split; [exact H1|]. split; [reflexivity|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
split; [exact H7|]. split; [|exact H9]. split; [exact Hwf|]. split; [|exact Hpd].
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hok r Hr) as Hokr.
apply regions_wf_In with (r := r) in Hwf as Hwfr; [|exact Hr].
apply (kregion_transport E m m' r Hokr Hwfr).
- intros x Hx. exact (Hm r x Hr Hx).
- intros x Hx Hwx. exact (Hw r x Hr Hx Hwx).
Qed.
(* A byte the world hides is never writable through the restricted view (the world hides no segment byte). *)
Lemma writable_unhidden : forall (W : world tfibsegs) m a, 0 <= a < 2 ^ 64 ->
writable_at tfibsegs (mrestrict (w_H W) m) a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W m a Ha Hw. destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [|reflexivity]. exfalso.
pose proof (w_Hoff W (Z_to_bv 64 a) Eh) as Hseg.
unfold writable_at, wview, mrestrict in Hw. rewrite Eh, Hseg in Hw. apply Hw. reflexivity.
Qed.
(* A byte store `sb x0, 0(rs1)` the walk meets at an address outside every region of the symbolic state (the engine
   stops with SR_addr there): the step writes 0 at it and the walk resumes after it. *)
Lemma kstore0 : forall (tbl : ctable) (W : world tfibsegs) E ss ms md (pc w : Z) (rs1 : bv 5) (a : Z),
table_ok tfibsegs tbl ->
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
clookup tbl pc = Some w -> is_ecall (Z_to_bv 32 w) = false ->
decode_any (Z_to_bv 32 w) = Some (Store SZ1 rs1 0%bv 0%bv, 4%Z) ->
getr (ms_regs ms) rs1 = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a ->
(forall r x, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= x < base_val E (YP09.r_base r) + YP09.r_hi r ->
Z_to_bv 64 x <> Z_to_bv 64 a) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [] (pc + 4)) (restrict (w_H W) ms1) /\
ms_regs ms1 = ms_regs ms /\
(forall x : word, ms_mem ms1 x = if bv_eqb x (Z_to_bv 64 a) then Some (Z_to_bv 8 0) else ms_mem ms x)).
Proof.
intros tbl W E ss ms md pc w rs1 a Htbl HS Hpc Hrv Hpc0 Hpc4 Hlk Hec Hdec R1 Ha Hwr Hout.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
pose proof (writable_unhidden W (ms_mem ms) a Ha Hwr) as Hh.
assert (Hav : v_addi (getr (ms_regs ms) rs1) (bv_signed (0%bv : bv 12)) = Z_to_bv 64 a).
{ rewrite R1. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity. }
assert (Hst : RiscvSemantics.store_ok tfibsegs (mrestrict (w_H W) (ms_mem ms))
(v_addi (getr (ms_regs ms) rs1) (bv_signed (0%bv : bv 12))) 1%nat = true).
{ rewrite Hav. unfold writable_at in Hwr. cbn [RiscvSemantics.store_ok].
destruct (wview tfibsegs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 a)); [reflexivity | congruence]. }
assert (Hmem : forall x : word, munrestrict (w_H W) (ms_mem ms)
(wbytes (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 a) (word_to_le_bytes 1 (getr (ms_regs ms) 0))) x =
if bv_eqb x (Z_to_bv 64 a) then Some (Z_to_bv 8 0) else ms_mem ms x).
{ intros x. unfold munrestrict. rewrite getr_zero.
assert (Hb : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0]) by (vm_compute; reflexivity).
rewrite Hb. cbn [wbytes].
destruct (bv_eqb x (Z_to_bv 64 a)) eqn:Ex.
- apply bv_eqb_eq in Ex. subst x. rewrite Hh. reflexivity.
- destruct (w_H W x) eqn:Ehx; [reflexivity|]. unfold mrestrict. rewrite Ehx. reflexivity. }
rewrite Hshape. eapply (SRr_step tfibsegs AF0x.Hwx_tfa W); [reflexivity | |].
- rewrite restrict_mkst_fx. cbn [ms_mem mkst].
apply (step_sb tfibsegs _ _ _ _ (Z_to_bv 32 w) rs1 0%bv 0%bv); [apply Htbl; exact Hlk | exact Hec | exact Hdec | exact Hst].
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm).
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|].
cbn [unrestrict ms_regs ms_mem mkst]. rewrite Hav. split; [|split; [reflexivity | exact Hmem]].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
set (m1 := wbytes (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 a) (word_to_le_bytes 1 (getr (ms_regs ms) 0))).
assert (Hm1 : forall x : word, mrestrict (w_H W) (munrestrict (w_H W) (ms_mem ms) m1) x =
if bv_eqb x (Z_to_bv 64 a) then Some (Z_to_bv 8 0) else mrestrict (w_H W) (ms_mem ms) x).
{ intros x. unfold mrestrict at 1. unfold m1. rewrite (Hmem x). destruct (bv_eqb x (Z_to_bv 64 a)) eqn:Ex.
+ apply bv_eqb_eq in Ex. subst x. rewrite Hh. reflexivity.
+ unfold mrestrict. destruct (w_H W x); reflexivity. }
replace (v_addi (Z_to_bv 64 pc) 4) with (Z_to_bv 64 (pc + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
change (bv_signed (Z_to_bv 12 4)) with 4; rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_pc_mem_out E ss (ms_regs ms) (Z_to_bv 64 pc) (pc + 4) _ _ HS).
+ intros r x Hr Hx. cbn [unrestrict ms_mem mkst]. unfold mbyte. rewrite (Hm1 (Z_to_bv 64 x)).
destruct (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 a)) eqn:Ex; [|reflexivity].
exfalso. apply bv_eqb_eq in Ex. exact (Hout r x Hr Hx Ex).
+ intros r x Hr Hx Hwx. cbn [unrestrict ms_mem mkst]. unfold writable_at, wview in *. rewrite (Hm1 (Z_to_bv 64 x)).
destruct (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 a)); [discriminate | exact Hwx].
Qed.
End k.
