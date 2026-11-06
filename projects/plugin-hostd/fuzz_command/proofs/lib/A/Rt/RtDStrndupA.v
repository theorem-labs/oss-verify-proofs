(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE7d.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE7d.v, with its numbers changed; 260 of its 343 lines of code are new or changed and 393 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAlloc RtDDefs RtDStrndupTbl RtDStrndupL.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PStrFun := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.

(* The strndup interceptor of plugin-hostd/fuzz_command's memory-checking image, from its trampoline to its call of
   the malloc interceptor's body, measured on the pinned image:

     45138 j 45710                                       the trampoline
     45710 addi sp,sp,-2032; sd ra,2024(sp) .. sd s8,1952(sp); addi s0,sp,2032; addi sp,sp,-128
     45744 mv s4,a1; mv s1,a0; jal 5f640                 TryAsanInitFromRtl (asan_inited = 1: returns 1)
     45750 beqz a0,457ac                                 not taken
     45754 mv a0,s1; mv a1,s4; jal 69d74                 internal_strnlen(x, n) = k, ra = 0x45760
     45760 mv s2,a0; addi s5,a0,1; mv a0,s5; jal 58b58   the malloc interceptor's body (k + 1), ra = 0x45770

   The frame is 2,160 bytes; TryAsanInitFromRtl writes 16 more below it, so the stretch writes only in
   [sp0 - 2176, sp0). The first part runs symbolically over tbl_snd; internal_strnlen (RtDStrndupL.v cmd_istrnlen)
   and the four instructions after it are stepped one at a time. *)
Definition SN_ENTRY : Z := 0x45138.
Definition SN_ISN : Z := 0x69d74.
Definition SN_RET1 : Z := 0x45760.
Definition SN_BODY : Z := 0x58b58.
Definition SN_MID : Z := 0x45770.
Definition SN_FRAME : Z := 2160.
Definition SN_WIN : Z := 2176.

Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- SN_WIN) 0 (- SN_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4)].
Definition ssA : sstate := mkSS SN_ENTRY sr_atoms (stkA :: map ro_region icpt_rodata) None (mkFacts factsA [] []).
Definition RUNTOA (s : sstate) := sym_run_toN tfibsegs tbl_snd FUEL SN_ISN s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOA ssA).
Lemma r_A : RUNTOA ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.

Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
(* ra, s0, s1 .. s8 are saved at these offsets below the caller's sp *)
Definition SAVEDA : list (Z * Z) :=
[(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72); (24, -80)].
Definition KEPTA : list Z := [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? SN_ISN) && match ss_resv ss with None => true | Some _ => false end &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - SN_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 1 (SLit SN_RET1) && reg_is ss 2 (SOff 2 (- SN_FRAME)) &&
reg_is ss 8 (SOff 2 0) && reg_is ss 9 (SOff 10 0) && reg_is ss 20 (SOff 11 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.

(* The frame-pointer chain the malloc body is called with: strndup's own record (sp0, the caller's ra and s0, which
   its prologue saves at sp0 - 8 and sp0 - 16), then the caller's chain, as UnwindFast reads it. *)
Definition snd_ch (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list (Z * Z * Z) :=
if frame0_ok ly regs then (spZ regs, raZ regs, s0Z regs) :: ch else [].

Lemma fpchain_ext : forall (ld ld' : Z -> option Z) lo top ch bp,
(forall a, lo <= a < top -> ld' a = ld a) -> lo + 16 <= bp -> bp <= top -> fpchain ld bp top ch -> fpchain ld' bp top ch.
Proof.
intros ld ld' lo top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hld Hbp Htp Hc; cbn [fpchain] in *.
- destruct Hc as (r & Hr & Hr0). exists r. rewrite Hld by lia. split; assumption.
- destruct Hc as (-> & Hal & H8 & H16 & Hra & Hn). split; [reflexivity|]. split; [exact Hal|].
rewrite !Hld by lia. split; [exact H8|]. split; [exact H16|]. split; [exact Hra|].
unfold bad_next in *. destruct ((nfp <=? bp) || (top - 16 <=? nfp) || negb (nfp mod 8 =? 0))%bool eqn:E; [exact Hn|].
apply orb_false_iff in E as [E _]. apply orb_false_iff in E as [E E2]. apply Z.leb_gt in E. apply Z.leb_gt in E2.
apply (IH nfp Hld ltac:(lia) ltac:(lia) Hn).
Qed.

(* The trace the body records for this call is the trace the contract names (RtAlloc.v:92 adup_trace). *)
Lemma snd_trace_eq : forall ly regs regs_c ch pc0 mid,
spZ regs_c = spZ regs - STRNDUP_FRAME -> raZ regs_c = mid -> 4096 <= mid ->
inner_trace ly pc0 regs_c (snd_ch ly regs ch) = adup_trace ly pc0 mid regs ch.
Proof.
intros ly regs regs_c ch pc0 mid Hsp Hra Hmid. unfold inner_trace, adup_trace, call_trace, snd_ch.
unfold frame0_ok at 1. rewrite Hsp, Hra.
destruct (spZ regs - STRNDUP_FRAME <=? ly_bot ly) eqn:E1; [reflexivity|]. cbn [orb].
destruct (ly_top ly - 16 <=? spZ regs - STRNDUP_FRAME) eqn:E2.
- apply Z.leb_le in E2. replace (spZ regs - STRNDUP_FRAME + 16 <? ly_top ly) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
- apply Z.leb_gt in E2. replace (mid <? 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
replace (spZ regs - STRNDUP_FRAME + 16 <? ly_top ly) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (frame0_ok ly regs); unfold unwind_of_chain; cbn [flat_map app]; reflexivity.
Qed.

Lemma snd_trace_len : forall ly pc0 mid regs ch, (length (adup_trace ly pc0 mid regs ch) <= kUnwindMax)%nat.
Proof.
intros ly pc0 mid regs ch. unfold adup_trace.
destruct ((spZ regs - STRNDUP_FRAME <=? ly_bot ly) || (ly_top ly - 16 <=? spZ regs - STRNDUP_FRAME) || (mid <? 4096))%bool;
[cbn [length]; unfold kUnwindMax; lia|].
destruct (frame0_ok ly regs); unfold unwind_of_chain; apply firstn_le_length.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mst_refl_pc' : forall regs (pc pc' : word) mem rom, bv_unsigned pc = bv_unsigned pc' ->
msteps tfibsegs (mkst regs pc mem rom) (mkst regs pc' mem rom).
Proof. intros regs pc pc' mem rom E. replace pc' with pc by (apply bv_eq; exact E). apply mst_refl. Qed.
(* internal_strnlen, then 0x45760 .. 0x4576c, up to the entry of the malloc body *)
Lemma pre_steps : forall (buf : list byte) (x n : Z) (m rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = w64 x -> getr regs 11 = w64 n -> getr regs 1 = w64 SN_RET1 ->
0 <= x < 2 ^ 64 -> 0 <= n < 2 ^ 32 ->
PStrFun.memchr_ok x 0 n buf ->
(forall j, (j < length buf)%nat -> (j <= Z.to_nat (PStrFun.strnlen_res n buf))%nat ->
rdn tfibsegs m (Z_to_bv 64 (x + Z.of_nat j)) 1 = Some [nth j buf NUL]) ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 SN_ISN) m rom) (mkst regs' (Z_to_bv 64 SN_BODY) m rom) /\
getr regs' 10 = w64 (PStrFun.strnlen_res n buf + 1) /\ getr regs' 1 = w64 SN_MID /\
getr regs' 18 = w64 (PStrFun.strnlen_res n buf) /\ getr regs' 21 = w64 (PStrFun.strnlen_res n buf + 1) /\
(forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 18%bv -> r <> 21%bv -> getr regs' r = getr regs r).
Proof.
intros buf x n m rom regs H10 H11 H1 Hx Hn Hok Hrd.
pose proof (strnlen_res_facts x n buf ltac:(lia) Hok) as (K0 & _).
set (k := PStrFun.strnlen_res n buf) in *.
destruct (cmd_istrnlen buf (w64 x) n m rom regs H10 H11 ltac:(lia)) as (regs1 & Hms1 & A10 & KEEP1).
- unfold w64. rewrite unsigned_lit_small by lia. exact Hok.
- intros j Hj Hjk. unfold w64. rewrite unsigned_lit_small by lia. apply Hrd; assumption.
- fold k in A10, KEEP1. rewrite H1 in Hms1.
replace (v_jalr (w64 SN_RET1) 0) with (Z_to_bv 64 SN_RET1 : word) in Hms1 by (apply bv_eq; vm_compute; reflexivity).
assert (E1 : getr regs1 1 = w64 SN_RET1) by (rewrite KEEP1 by reg_neq_tac; exact H1).
eexists. split.
+ eapply msteps_trans; [exact Hms1|]. unfold SN_RET1. norm_pc.
sv S_45760 DS_45760 (Z_to_bv 64 k).
sv S_45764 DS_45764 (Z_to_bv 64 (k + 1)).
sv S_45768 DS_45768 (Z_to_bv 64 (k + 1)).
stepj' S_4576c DS_4576c.
apply mst_refl_pc'. vm_compute. reflexivity.
+ split; [gr; reflexivity|]. split; [gr; apply bv_eq; vm_compute; reflexivity|].
split; [gr; reflexivity|]. split; [gr; reflexivity|].
intros r Q1 Q10 Q12 Q13 Q18 Q21. rewrite ?getr_other by assumption. apply KEEP1; assumption.
Qed.
End s.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); reflexivity. Qed.

Lemma rdn1_of_aview : forall H (m : word -> option byte) a (b : byte),
aview tfibsegs H m a = Some (bv_unsigned b) -> rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros H m a b Hv. apply AF0x.aview_some in Hv as (b' & Hb' & E).
assert (Eb : b' = b) by (apply bv_eq; exact E). subst b'.
apply (proj2 (rdn_mbytes tfibsegs _ 1 a [b])). split; [reflexivity|]. intros i Hi. destruct i; [|lia].
cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact Hb'.
Qed.

(* From the trampoline to the entry of the malloc body: the state the body's contract (RtDDefs.v:71) is applied to.
   The source premise is the one internal_strnlen needs: every byte it reads (index at most k, inside the buffer)
   is visible and outside the 2,176 bytes this stretch writes. *)
Theorem snd_pre : forall ly S (W : world tfibsegs) regs mem md x n buf ch,
acall_pre tfibsegs B ly S W regs mem md ch ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x < 2 ^ 63 ->
PStrFun.memchr_ok x 0 n buf ->
(forall j, (j < length buf)%nat -> (j <= Z.to_nat (PStrFun.strnlen_res n buf))%nat ->
aview tfibsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j buf NUL)) /\
~ (spZ regs - SN_WIN <= x + Z.of_nat j < spZ regs)) ->
SRr tfibsegs W (cfg_at tfibsegs SN_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs_c mem_c md_c,
c' = cfg_at tfibsegs SN_BODY regs_c mem_c md_c /\
acall_pre_w tfibsegs B MALLOC_IN_STK ly S W regs_c mem_c md_c (snd_ch ly regs ch) /\
getr regs_c 10 = w64 (PStrFun.strnlen_res n buf + 1) /\ getr regs_c 1 = w64 SN_MID /\
getr regs_c 2 = w64 (spZ regs - SN_FRAME) /\ getr regs_c 8 = w64 (spZ regs) /\ getr regs_c 9 = w64 x /\
getr regs_c 18 = w64 (PStrFun.strnlen_res n buf) /\ getr regs_c 20 = w64 n /\
getr regs_c 21 = w64 (PStrFun.strnlen_res n buf + 1) /\
(forall r : bv 5, In r [3%bv; 4%bv; 19%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr regs_c r = getr regs r) /\
same_but_materialized md md_c /\
(forall z : word, ~ (spZ regs - SN_WIN <= bv_unsigned z < spZ regs) -> mem_c z = mem z) /\
(forall a, spZ regs - SN_WIN <= a < spZ regs -> apresent (w_H W) mem_c a) /\
(forall j rz off, nth_error SAVEDA j = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W) mem_c) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz))))).
Proof.
intros ly S W regs mem md x n buf ch HPRE G10 G11 Hn Hx Hok Hsrc.
pose proof HPRE as (HAR & Hreg & Hra' & Hal16 & Hslo & Hbot & Htop & HpresA & Hgp & Htp & Hch & Hqm).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ASTACK in Hslo, HpresA.
pose (H := w_H W).
assert (Hsp : 2 ^ 44 <= spZ regs <= 2 ^ 47) by lia.
set (sp0 := spZ regs) in *.
unfold cfg_at. change (w64 SN_ENTRY) with (Z_to_bv 64 SN_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 n) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
(* the symbolic stretch, from the trampoline to the call of internal_strnlen *)
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 SN_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (icpt_rodata_ok B TB ly S H mem EE (proj1 HAR))].
unfold stkA, SN_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2176)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply HpresA. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, icpt_rodata, ro_region, extent_of_region, SN_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; first [exact Hal16 | lia]. }
eapply SRr_bind; [apply (snd_phase_to W EE SN_ISN _ _ _ _ _ HS0 r_A)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - SN_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SN_WIN) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold SN_WIN in *. lia. }
clear HF1 HFr1.
(* the state at the call of internal_strnlen, read off shapeA *)
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK].
apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh Smem]. apply andb_prop in Hsh as [Hpc _].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is eA (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hr. rewrite (RD r _ Hr). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. apply (RA r i Hi). rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK. rewrite <- Hi. exact HK. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
assert (W10 : getr (ms_regs ms1) 10 = w64 x).
{ rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (W11 : getr (ms_regs ms1) 11 = w64 n).
{ rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (W1 : getr (ms_regs ms1) 1 = w64 SN_RET1) by (rewrite (RD 1%bv (SLit SN_RET1) R1); reflexivity).
assert (W2 : getr (ms_regs ms1) 2 = w64 (sp0 - SN_FRAME)).
{ rewrite (RD 2%bv (SOff 2 (- SN_FRAME)) R2). cbn [sv_denot]. rewrite EE2. reflexivity. }
assert (W8 : getr (ms_regs ms1) 8 = w64 sp0).
{ rewrite (RD 8%bv (SOff 2 0) R8). cbn [sv_denot]. rewrite EE2, Z.add_0_r. reflexivity. }
assert (W9 : getr (ms_regs ms1) 9 = w64 x).
{ rewrite (RD 9%bv (SOff 10 0) R9). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
assert (W20 : getr (ms_regs ms1) 20 = w64 n).
{ rewrite (RD 20%bv (SOff 11 0) R20). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
(* internal_strnlen and the call of the malloc body *)
pose proof (strnlen_res_facts x n buf ltac:(lia) Hok) as (K0 & _).
destruct (pre_steps buf x n (mrestrict H (ms_mem ms1)) (seg_rom tfibsegs) (ms_regs ms1) W10 W11 W1 ltac:(lia) Hn Hok)
as (regs2 & Hms & A10 & A1 & A18 & A21 & KEEP2).
{ intros j Hj Hjk. destruct (Hsrc j Hj Hjk) as [Hv Hw]. apply rdn1_of_aview. rewrite (aview_same H mem (ms_mem ms1)); [exact Hv|].
apply MEQ1. rewrite unsigned_lit_small by lia. exact Hw. }
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb _ model' Hsbm). rewrite ?wvb_wvb.
cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H (ms_mem ms1) (mrestrict H (ms_mem ms1))).
assert (M2 : forall z, mem2 z = ms_mem ms1 z) by (intros z; subst mem2; apply munrestrict_mrestrict_same).
assert (AV2 : forall a, aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a) by (intros a; apply aview_same; apply M2).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SN_WIN <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (K2 : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA ->
r <> 1%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 18%bv -> r <> 21%bv -> getr regs2 r = getr regs r).
{ intros r i Hi Hin Q1 Q10 Q12 Q13 Q18 Q21. rewrite (KEEP2 r Q1 Q10 Q12 Q13 Q18 Q21). exact (RK r i Hi Hin). }
assert (P2 : getr regs2 2 = w64 (sp0 - SN_FRAME)) by (rewrite KEEP2 by reg_neq_tac; exact W2).
assert (Hsp2 : spZ regs2 = sp0 - SN_FRAME) by (unfold spZ; rewrite P2; unfold w64, SN_FRAME; apply unsigned_lit_small; lia).
assert (P8 : getr regs2 8 = w64 sp0) by (rewrite KEEP2 by reg_neq_tac; exact W8).
assert (Hs02 : s0Z regs2 = sp0) by (unfold s0Z; rewrite P8; unfold w64; apply unsigned_lit_small; lia).
assert (PRES1 : forall a, sp0 - SN_WIN <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, SN_WIN in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold SN_WIN in *. lia. }
assert (PRES2 : forall a, sp0 - SN_WIN <= a < sp0 -> apresent H mem2 a) by (intros a Ha; apply (apresent_same H (ms_mem ms1) mem2 a (M2 _)); apply PRES1, Ha).
assert (AVhi : forall a, sp0 <= a < 2 ^ 64 -> aview tfibsegs H mem2 a = aview tfibsegs H mem a) by (intros a Ha; rewrite AV2; apply AV1; lia).
assert (CK2 : forall j rz off, nth_error SAVEDA j = Some (rz, off) ->
val_mem tfibsegs (mrestrict H mem2) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. apply (AF0x.val_mem_ext (mrestrict H (ms_mem ms1))); [|exact (CK j rz off Hj)].
intros q _. apply AF0x.mbyte_mrestrict_same. apply M2. }
apply SRr_ret. split; [reflexivity|].
exists regs2, mem2, (with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md).
split; [reflexivity|].
split.
{ (* the body's precondition *)
split.
{ apply (al_frame _ _ LAWS ly S W mem md mem2 _ HAR).
+ intros a Hr Hown. rewrite AV2. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0, SN_WIN in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
rewrite AV2. destruct (Z_lt_le_dec a' (sp0 - SN_WIN)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRES1. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
+ exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresA ltac:(unfold SN_WIN; lia) ltac:(lia)) (AE2y.hs_kept_eq _ _ _ M2)). }
split; [exact Hreg|].
split; [rewrite A1; unfold w64, SN_MID; apply ret_ok_lit; [lia | reflexivity]|].
split; [rewrite Hsp2; unfold SN_FRAME; replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite Hsp2; unfold MALLOC_IN_STK, SN_FRAME; lia|].
split; [rewrite Hsp2; unfold SN_FRAME; lia|].
split.
{ intros a Ha. rewrite Hsp2 in Ha. unfold MALLOC_IN_STK, SN_FRAME in Ha.
destruct (Z_lt_le_dec a (sp0 - SN_WIN)) as [L1|L1].
+ apply (apresent_same H mem mem2 a). { rewrite M2. apply MEQ1. rewrite unsigned_lit_small by lia. unfold SN_WIN in *; lia. } apply HpresA. lia.
+ apply PRES2. unfold SN_WIN in *; lia. }
split; [rewrite (K2 3%bv 3%nat eq_refl ltac:(cbn; tauto)) by reg_neq_tac; exact Hgp|].
split; [rewrite (K2 4%bv 4%nat eq_refl ltac:(cbn; tauto)) by reg_neq_tac; exact Htp|].
split; [|exact Hqm].
(* the chain: strndup's own record, then the caller's *)
destruct Hch as (Hra4 & Hch).
unfold chain_pre. split; [unfold raZ; rewrite A1; unfold w64, SN_MID; rewrite unsigned_lit_small by lia; lia|].
unfold frame0_ok at 1. rewrite Hsp2. unfold SN_FRAME.
unfold snd_ch. unfold frame0_ok in Hch |- *. fold sp0 in Hch |- *.
destruct (sp0 - 2160 + 16 <? ly_top ly) eqn:F2.
- unfold bad_next at 1. rewrite ?Hsp2, ?Hs02. unfold SN_FRAME.
replace (sp0 <=? sp0 - 2160) with false by (symmetry; apply Z.leb_gt; lia).
replace (sp0 mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; replace sp0 with (8 * (2 * (sp0 / 16)) + 2 * (sp0 mod 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia); rewrite Hal16; rewrite Z.add_0_r, Z.mul_comm, Z_mod_mult; reflexivity).
destruct (sp0 + 16 <? ly_top ly) eqn:F0.
+ apply Z.ltb_lt in F0. replace (ly_top ly - 16 <=? sp0) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb negb].
split; [lia|]. cbn [fpchain]. split; [reflexivity|].
split; [replace sp0 with (8 * (2 * (sp0 / 16)) + 2 * (sp0 mod 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia); rewrite Hal16, Z.add_0_r, Z.mul_comm, Z_mod_mult; reflexivity|].
split.
{ apply AF0x.val_mem_rdword; [apply u64_range|]. pose proof (CK2 0%nat 1 (-8) eq_refl) as V. replace (sp0 + -8) with (sp0 - 8) in V by lia. exact V. }
split.
{ apply AF0x.val_mem_rdword; [apply u64_range|]. pose proof (CK2 1%nat 8 (-16) eq_refl) as V. replace (sp0 + -16) with (sp0 - 16) in V by lia. exact V. }
split; [exact Hra4|].
destruct (bad_next sp0 (ly_top ly) (s0Z regs)) eqn:BN; [exact Hch|].
destruct Hch as (Hle & Hfp).
apply (fpchain_ext (rdword (aview tfibsegs H mem)) _ sp0 (ly_top ly) ch (s0Z regs)); [| lia | | exact Hfp].
* intros a Ha. unfold rdword. rewrite !AVhi by lia. reflexivity.
* unfold bad_next in BN. apply orb_false_iff in BN as [BN _]. apply orb_false_iff in BN as [_ BN]. apply Z.leb_gt in BN. lia.
+ apply Z.ltb_ge in F0. replace (ly_top ly - 16 <=? sp0) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- apply Z.ltb_ge in F2. replace (sp0 + 16 <? ly_top ly) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
split; [exact A10|]. split; [exact A1|]. split; [exact P2|]. split; [exact P8|].
split; [rewrite KEEP2 by reg_neq_tac; exact W9|]. split; [exact A18|].
split; [rewrite KEEP2 by reg_neq_tac; exact W20|]. split; [exact A21|].
split.
{ intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
- exact (K2 3%bv 3%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 4%bv 4%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 19%bv 19%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 22%bv 22%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 23%bv 23%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 24%bv 24%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 25%bv 25%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 26%bv 26%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)).
- exact (K2 27%bv 27%nat eq_refl ltac:(cbn; tauto) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac) ltac:(reg_neq_tac)). }
split; [apply with_vm_backing_same|].
split; [intros z Hz; rewrite M2; apply MEQ1; exact Hz|].
split; [exact PRES2|].
exact CK2.
Qed.
End g.
