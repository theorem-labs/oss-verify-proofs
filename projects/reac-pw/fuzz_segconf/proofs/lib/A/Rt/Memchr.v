(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6x.v's walk of the memchr wrapper, generalised to any byte c in a1 and to a window that may hold no c: the musl call is MemchrMusl's walk, and after it the found case keeps AE6x's check (AE6y, count a0 - s2 + 1) while the not-found case takes the twin check of MemchrChk (count s1). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_disco/lib/A/Rt/Memchr.v
   (the other lanes' general memchr), with its module paths changed and its seven addresses moved to fuzz_command.asan by code pairing: trampoline 0x429dc -> 0x45158, musl memchr 0x99674 -> 0x9ea40, return 0x441fc -> 0x47b8c, epilogue 0x4425c -> 0x47bec, REAL(memchr) cell 0xa2238 -> 0xa8158, and the musl mask window 0x10368/0x10388 -> 0x10358/0x10378 (AE39.v mc_bounds). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/Memchr.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE39 AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AE3a AE6y.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import MemchrMusl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require MemchrChk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition MCH_ENTRY : Z := 0x43a3c.
Definition MCH_REAL : Z := 0x9a2f8.
Definition MCH_RET : Z := 0x46f98.
Definition MCH_END : Z := 0x46ff8.
Definition MCH_WIN : Z := 2144.
Definition MCH_SCR : Z := 2200.
Definition mchr_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [(0xa47a8, 8, [(0, 8%N, 0x9a2f8)])].
Lemma mchr_rodata_chk : forall ly, rodata_chk ly mchr_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- MCH_WIN) 0 (- MCH_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 (2^47) 0); (12%nat, mkAF 0 (2^32 - 1) 0)].
Definition ssA : sstate := mkSS MCH_ENTRY sr_atoms (stkA :: map ro_region mchr_rodata) None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_icpt FUEL MCH_REAL s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A : RUNTOR ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2120 (CVal 8 (SOff 32 0)); YP09.mkChunk 2112 (CVal 8 (SOff 33 0)); YP09.mkChunk 2104 (CVal 8 (SOff 34 0));
YP09.mkChunk 2096 (CVal 8 (SOff 35 0)); YP09.mkChunk 2088 (CVal 8 (SOff 36 0)); YP09.mkChunk 2080 (CVal 8 (SOff 37 0));
YP09.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi : sstate := mkSS MCH_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? MCH_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - MCH_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 1 (SLit MCH_RET) && reg_is ss 2 (SOff 2 (-2128)) &&
reg_is ss 18 (SOff 10 0) && reg_is ss 20 (SLit 1) && reg_is ss 9 (SOff 12 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma rdn1_mbyte : forall (m : word -> option byte) a,
rdn tfibsegs m (Z_to_bv 64 a) 1 = match mbyte tfibsegs m a with Some b => Some [b] | None => None end.
Proof.
intros m a. cbn [rdn]. change (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom tfibsegs (Z_to_bv 64 a) end) with (mbyte tfibsegs m a).
destruct (mbyte tfibsegs m a); reflexivity.
Qed.
Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); reflexivity. Qed.
Lemma first_idx_ex : forall (g : Z -> Z) (c n : Z), 0 <= n ->
exists k, 0 <= k <= n /\ (forall i, 0 <= i < k -> g i <> c) /\ (k < n -> g k = c).
Proof.
intros g c n Hn. remember (Z.to_nat n) as d eqn:Hd. revert n Hn Hd.
induction d as [|d IH]; intros n Hn Hd.
- exists 0. split; [lia|]. split; [intros i Hi; lia | intros Hlt; lia].
- destruct (IH (n - 1) ltac:(lia) ltac:(lia)) as (k & Hk & Hbef & Hat).
destruct (Z_lt_le_dec k (n - 1)) as [Hlt|Hge].
+ exists k. split; [lia|]. split; [exact Hbef | intros _; apply Hat; lia].
+ assert (Hkn : k = n - 1) by lia.
destruct (Z.eq_dec (g (n - 1)) c) as [Heq|Hne].
* exists (n - 1). split; [lia|]. split; [rewrite <- Hkn; exact Hbef | intros _; exact Heq].
* exists n. split; [lia|]. split; [|intros Hlt; lia].
intros i Hi. destruct (Z.eq_dec i (n - 1)) as [->|Hne2]; [exact Hne|]. apply Hbef. lia.
Qed.
Lemma shadow_addr_mono : forall a b, a <= b -> shadow_addr a <= shadow_addr b.
Proof. intros a b Hab. unfold shadow_addr. pose proof (Z.div_le_mono a b 8 ltac:(lia) Hab). lia. Qed.
End f.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.
Definition POSTC (ly : alayout) (S : astate) (W : world tfibsegs) (regs2 : bvmap 5 word)
(mem2 : word -> option byte) (md2 : Model) (res : Z) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs3 mem3 md3,
c' = cfg_at tfibsegs MCH_END regs3 mem3 md3 /\
AR tfibsegs B ly S W mem3 md3 /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 20 -> r <> 21 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) /\
same_but_materialized md2 md3 /\
getr regs3 10 = w64 res /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs2 - 72 <= a < spZ regs2) -> aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a) /\
(forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a).
Lemma chk_found : forall ly S W regs2 mem2 md2 x nn,
AR tfibsegs B ly S W mem2 md2 -> spZ regs2 mod 16 = 0 ->
ly_stk_lo ly + 72 <= spZ regs2 -> spZ regs2 <= ly_stk_hi ly ->
(forall a, spZ regs2 - 72 <= a < spZ regs2 -> apresent (w_H W) mem2 a) ->
getr regs2 10 = w64 (x + nn - 1) -> getr regs2 18 = w64 x -> getr regs2 20 = w64 1 ->
0 < x -> 1 <= nn < 2 ^ 32 -> x + nn <= 2 ^ 63 -> amem_range x nn ->
range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF x nn ->
shadow_hull_vis (aview tfibsegs (w_H W) mem2) x nn ->
SRr tfibsegs W (cfg_at tfibsegs MCH_RET regs2 mem2 md2) (POSTC ly S W regs2 mem2 md2 (x + nn - 1)).
Proof.
intros ly S W regs2 mem2 md2 x nn HAR Hal Hslo Hshi Hpres GN GP G20 Hx Hnn Hxn HAM HRA HHULL.
eapply SRr_bind.
{ change MCH_RET with AE6y.RC_ENTRY. assert (Hp0 : 0 <= x) by lia.
eapply AE6y.mchr_check_srr; eassumption. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HAR3|]. split; [exact KEPT3|]. split; [exact Hsbm3|].
split; [rewrite A10'; exact GN|]. split; [exact Hfr3 | exact Hpres3].
Qed.
Lemma chk_none : forall ly S W regs2 mem2 md2 x nn,
AR tfibsegs B ly S W mem2 md2 -> spZ regs2 mod 16 = 0 ->
ly_stk_lo ly + 72 <= spZ regs2 -> spZ regs2 <= ly_stk_hi ly ->
(forall a, spZ regs2 - 72 <= a < spZ regs2 -> apresent (w_H W) mem2 a) ->
getr regs2 10 = w64 0 -> getr regs2 18 = w64 x -> getr regs2 20 = w64 1 -> getr regs2 9 = w64 nn ->
0 < x -> 1 <= nn < 2 ^ 32 -> x + nn <= 2 ^ 63 -> amem_range x nn ->
range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF x nn ->
shadow_hull_vis (aview tfibsegs (w_H W) mem2) x nn ->
SRr tfibsegs W (cfg_at tfibsegs MCH_RET regs2 mem2 md2) (POSTC ly S W regs2 mem2 md2 0).
Proof.
intros ly S W regs2 mem2 md2 x nn HAR Hal Hslo Hshi Hpres GN GP G20 G9 Hx Hnn Hxn HAM HRA HHULL.
eapply SRr_bind.
{ change MCH_RET with MemchrChk.RC_ENTRY. assert (Hp0 : 0 <= x) by lia.
eapply MemchrChk.mchr_check_srr; eassumption. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HAR3|]. split; [exact KEPT3|]. split; [exact Hsbm3|].
split; [exact A10'|]. split; [exact Hfr3 | exact Hpres3].
Qed.
Lemma chk_zero : forall ly S W regs2 mem2 md2 x,
AR tfibsegs B ly S W mem2 md2 -> spZ regs2 mod 16 = 0 ->
ly_stk_lo ly + 72 <= spZ regs2 -> spZ regs2 <= ly_stk_hi ly ->
(forall a, spZ regs2 - 72 <= a < spZ regs2 -> apresent (w_H W) mem2 a) ->
getr regs2 10 = w64 0 -> getr regs2 18 = w64 x -> getr regs2 20 = w64 1 -> getr regs2 9 = w64 0 ->
0 <= x <= 2 ^ 47 ->
SRr tfibsegs W (cfg_at tfibsegs MCH_RET regs2 mem2 md2) (POSTC ly S W regs2 mem2 md2 0).
Proof.
intros ly S W regs2 mem2 md2 x HAR Hal Hslo Hshi Hpres GN GP G20 G9 Hxb.
eapply SRr_bind.
{ change MCH_RET with MemchrChk.RC_ENTRY.
eapply MemchrChk.mchr_check0_srr; eassumption. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10' & Hfr3 & Hpres3).
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [reflexivity|]. split; [exact HAR3|]. split; [exact KEPT3|]. split; [exact Hsbm3|].
split; [exact A10'|]. split; [exact Hfr3 | exact Hpres3].
Qed.
Lemma mch_tail : forall ly S (W : world tfibsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 x c n k,
ecall_pre tfibsegs B ly S W regs mem md ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
0 <= k <= n ->
(forall i, 0 <= i < k -> exists b, aview tfibsegs (w_H W) mem (x + i) = Some b /\ b <> c) ->
(k < n -> aview tfibsegs (w_H W) mem (x + k) = Some c) ->
src_ok tfibsegs W regs mem x n -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
mconsts_view W mem ->
getr regs1 10 = w64 x -> getr regs1 11 = w64 c -> getr regs1 12 = w64 n -> getr regs1 9 = w64 n ->
getr regs1 1 = w64 MCH_RET -> getr regs1 2 = w64 (spZ regs - 2128) -> getr regs1 18 = w64 x -> getr regs1 20 = w64 1 ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 22 = getr regs 22 -> getr regs1 23 = getr regs 23 -> getr regs1 24 = getr regs 24 ->
getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MCH_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MCH_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MCH_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = (if k <? n then w64 (x + k) else w64 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 x c n k HPRE Hc Hn Hx Hxn Hk Hbef Hat Hsrc Ham Hra Hhull Hrom
G10 G11 G12 G9 G1 G2 G18 G20 G3 G4 G22 G23 G24 G25 G26 G27 MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK, MCH_WIN in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
assert (Hamr : x + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfibsegs H mem1 a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (SRCW : forall a, x <= a < x + n -> ~ (sp0 - 2144 <= a < sp0)) by (intros a Ha; destruct (Hsrc a Ha) as [_ Hns]; unfold ESTACK in Hns; unfold sp0 in *; lia).
set (f := fun i : Z => match mbyte tfibsegs (mrestrict H mem1) (x + i) with Some b => b | None => NUL end).
assert (FB : forall i, 0 <= i < n -> aview tfibsegs H mem1 (x + i) = Some (bv_unsigned (f i)) /\
mbyte tfibsegs (mrestrict H mem1) (x + i) = Some (f i)).
{ intros i Hi. assert (Hv : aview tfibsegs H mem1 (x + i) <> None).
{ rewrite AV1; [apply (proj1 (Hsrc (x + i) ltac:(lia))) | lia | apply SRCW; lia]. }
destruct (aview tfibsegs H mem1 (x + i)) as [b|] eqn:Eb; [|exfalso; exact (Hv eq_refl)].
destruct (proj1 (aview_some H mem1 (x + i) b) Eb) as (bb & Hbb & Hval).
subst f. cbn beta. rewrite Hbb. split; [rewrite Hval; reflexivity | reflexivity]. }
assert (BS : forall i, 0 <= i < n -> rdn tfibsegs (mrestrict H mem1) (Z_to_bv 64 (x + i)) 1 = Some [f i]).
{ intros i Hi. rewrite rdn1_mbyte, (proj2 (FB i Hi)). reflexivity. }
assert (HROM : forall a : Z, tfib_D_const_HIGHS_0x8080808080808080 <= a < tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs (mrestrict H mem1) (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1).
{ intros a Ha.
assert (Hin : MC_LO <= a < MC_HI) by (unfold MC_LO, MC_HI; lia).
pose proof (Hrom a Hin) as Hv. fold H in Hv. rewrite <- (AV1 a) in Hv
by (unfold tfib_D_const_HIGHS_0x8080808080808080, tfib_D_const_ONES_0x0101010101010100 in Ha; unfold sp0 in *; lia).
rewrite !rdn1_mbyte. unfold aview in Hv.
change (mbyte tfibsegs (fun _ : word => None) a) with (seg_rom tfibsegs (Z_to_bv 64 a)).
destruct (mbyte tfibsegs (mrestrict H mem1) a) as [b|], (seg_rom tfibsegs (Z_to_bv 64 a)) as [b'|]; cbn in Hv; try discriminate; [|reflexivity].
injection Hv as Hv. do 2 f_equal. apply bv_eq. exact Hv. }
assert (HKB : forall i, 0 <= i < k -> bv_unsigned (f i) <> c).
{ intros i Hi. destruct (Hbef i Hi) as (b & Hb & Hb0).
rewrite <- (AV1 (x + i)) in Hb by (try lia; apply SRCW; lia).
rewrite (proj1 (FB i ltac:(lia))) in Hb. injection Hb as Hb. rewrite Hb. exact Hb0. }
assert (HKA : k < n -> bv_unsigned (f k) = c).
{ intros Hlt. pose proof (Hat Hlt) as Hb.
rewrite <- (AV1 (x + k)) in Hb by (try lia; apply SRCW; lia).
rewrite (proj1 (FB k ltac:(lia))) in Hb. injection Hb as Hb. exact Hb. }
destruct (disco_memchr (w64 x) n c k f (mrestrict H mem1) (seg_rom tfibsegs) regs1 Hc ltac:(lia)) as (regs2 & Hms & A10 & KEEP).
- unfold w64. rewrite unsigned_lit_small by lia. lia.
- intros i Hi. unfold w64. rewrite unsigned_lit_small by lia. apply BS. exact Hi.
- exact HROM.
- exact Hk.
- exact HKB.
- exact HKA.
- exact G10.
- exact G11.
- exact G12.
-
rewrite G1 in Hms. replace (v_jalr (w64 MCH_RET) 0) with (Z_to_bv 64 MCH_RET : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_musl_memchr) with (Z_to_bv 64 MCH_REAL) in Hms.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb _ model' Hsbm). rewrite ?wvb_wvb.
cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H mem1 (mrestrict H mem1)).
assert (M2 : forall z, mem2 z = mem1 z) by (intros z; subst mem2; apply munrestrict_mrestrict_same).
assert (AV2 : forall a, aview tfibsegs H mem2 a = aview tfibsegs H mem1 a) by (intros a; apply aview_same; apply M2).
assert (KEEPr : forall r : bv 5, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs2 r = getr regs1 r) by (intros r; apply KEEP).
assert (R2sp : spZ regs2 = sp0 - 2128).
{ unfold spZ. rewrite KEEPr by (intros H'; discriminate H'). rewrite G2. unfold w64. apply unsigned_lit_small. lia. }
assert (A10' : getr regs2 10 = w64 (if k <? n then x + k else 0)).
{ rewrite A10. unfold w64. destruct (k <? n); [rewrite unsigned_lit_small by lia|]; reflexivity. }
assert (HARm : AR tfibsegs B ly S W mem2 (with_vm_backing (m_vm_lazy md) (m_vm_materialized model') md)).
{ apply (al_frame _ _ LAWS ly S W mem md mem2 _ HAR).
- intros a Hr Hown. rewrite AV2. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
- intros a Hv. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
rewrite AV2. destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
- apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
- apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
- apply (same_but_materialized_frame md _ (with_vm_backing_same md (m_vm_materialized model'))).
- exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(lia) ltac:(lia)) (AE2y.hs_kept_eq _ _ _ M2)). }
assert (HALm : spZ regs2 mod 16 = 0).
{ rewrite R2sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
assert (HSLOm : ly_stk_lo ly + 72 <= spZ regs2) by (rewrite R2sp; unfold sp0 in *; lia).
assert (HSHIm : spZ regs2 <= ly_stk_hi ly) by (rewrite R2sp; unfold sp0 in *; lia).
assert (HPRESm : forall a, spZ regs2 - 72 <= a < spZ regs2 -> apresent H mem2 a).
{ intros a Ha. rewrite R2sp in Ha.
apply (apresent_same H mem1 mem2 a (M2 _)).
destruct (Z_lt_le_dec a (sp0 - 2144)) as [L1|L1].
- apply (apresent_same H mem mem1 a). { apply MEQ1. rewrite unsigned_lit_small by lia. lia. } apply HpresE. unfold sp0 in *. lia.
- apply PRS1. lia. }
assert (HG18 : getr regs2 18 = w64 x) by (rewrite KEEPr by (intros H'; discriminate H'); exact G18).
assert (HG20 : getr regs2 20 = w64 1) by (rewrite KEEPr by (intros H'; discriminate H'); exact G20).
assert (HG9 : getr regs2 9 = w64 n) by (rewrite KEEPr by (intros H'; discriminate H'); exact G9).
assert (AVm : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a)
by (intros a Hr Ha; rewrite AV2; apply AV1; assumption).
assert (HRAm : forall m, 0 <= m <= n -> range_addressable (aview tfibsegs H mem2) SHADOW_OFF x m).
{ intros m Hm. eapply range_addressable_agree; [|eapply range_addressable_sub; [exact Hra | lia | lia]].
intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
apply AVm; unfold sp0 in *; lia. }
assert (HHULLm : forall m, 0 < m <= n -> shadow_hull_vis (aview tfibsegs H mem2) x m).
{ intros m Hm s Hs. rewrite AVm; [apply (Hhull ltac:(lia)); unfold shadow_hull_vis in *|..];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2];
pose proof (shadow_addr_bounds (x + m - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as [U1 U2];
unfold kLowMemEnd, kHighShadowEnd in *;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + m - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + m - 1)) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia));
pose proof (shadow_addr_mono x (x + m - 1) ltac:(lia)); pose proof (shadow_addr_mono (x + m - 1) (x + n - 1) ltac:(lia));
unfold sp0 in *; lia. }
assert (HAMm : forall m, 0 <= m <= n -> amem_range x m)
by (intros m Hm; unfold amem_range in *; lia).
eapply SRr_bind with (R := POSTC ly S W regs2 mem2 _ (if k <? n then x + k else 0)).
{ destruct (Z_lt_le_dec k n) as [Hfound|Hnone].
- replace (if k <? n then x + k else 0) with (x + (k + 1) - 1)
by (replace (k <? n) with true by (symmetry; apply Z.ltb_lt; lia); f_equal; lia).
apply (chk_found ly S W regs2 mem2 _ x (k + 1) HARm HALm HSLOm HSHIm HPRESm);
[ replace (x + (k + 1) - 1) with (x + k) by lia;
rewrite A10'; replace (k <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
| exact HG18 | exact HG20 | lia | lia | lia | apply HAMm; lia | apply HRAm; lia | apply HHULLm; lia ].
- replace (if k <? n then x + k else 0) with 0
by (replace (k <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
destruct (Z.eq_dec n 0) as [Hz|Hpos].
+ apply (chk_zero ly S W regs2 mem2 _ x HARm HALm HSLOm HSHIm HPRESm);
[ rewrite A10'; replace (k <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
| exact HG18 | exact HG20 | rewrite HG9, Hz; reflexivity | lia ].
+ apply (chk_none ly S W regs2 mem2 _ x n HARm HALm HSLOm HSHIm HPRESm);
[ rewrite A10'; replace (k <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
| exact HG18 | exact HG20 | exact HG9 | lia | lia | lia | apply HAMm; lia | apply HRAm; lia | apply HHULLm; lia ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KEPT3 & Hsbm3 & A10'' & Hfr3 & Hpres3).
rewrite R2sp in Hfr3.
set (E4 := Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (K3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 18 -> z <> 20 -> z <> 21 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5 H6. exact (KEPT3 z H1 H2 H3 H5 H6). }
assert (R3sp : getr regs3 2 = w64 (sp0 - 2128)).
{ rewrite (K3 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ subst E4. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R3sp. unfold w64. apply unsigned_lit_small. lia. }
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2200 <= a < sp0 - 2128) -> mbyte tfibsegs (mrestrict H mem3) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. apply mbyte_of_aview. rewrite <- (AV2 a). apply Hfr3; [exact Hr | clear -Ha; lia]. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - 64 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem3) a 8 v).
{ intros a v Hv Hlo Hhi. apply (AF0x.val_mem_ext (mrestrict H mem1)); [|exact Hv]. intros j Hj. apply MB3; lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs3 (w64 MCH_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs3 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2128) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem3) (sp0 - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs3 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VM; [exact Hv | lia | lia]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact V6].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
unfold cfg_at.
eapply SRr_bind; [apply (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21.
rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23. rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs3 _ 0)).
rewrite X32 in Q1.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs3 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs3 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs3 _ ii rr Hnth)).
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem3 a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split]]]].
+   apply (al_frame _ _ LAWS ly S W mem3 md3 (ms_mem ms4) _ HAR3).
* intros a Hr Hown. apply AV4.
* intros a Hv. rewrite AV4. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ4).
+
intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl), (K3 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl), (K3 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
* assert (Hcs : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22, (Y 22%nat 22%bv eq_refl), (K3 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G22.
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23, (Y 23%nat 23%bv eq_refl), (K3 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G23.
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (Y 24%nat 24%bv eq_refl), (K3 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G24.
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl), (K3 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G25.
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl), (K3 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G26.
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl), (K3 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite KEEPr by (intros H'; discriminate H'). exact G27.
+ eapply same_but_materialized_trans; [exact Hsbm3 | apply with_vm_backing_same].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl), A10''. destruct (k <? n); reflexivity.
+ intros a Hr Hs. rewrite AV4. rewrite Hfr3 by (unfold sp0 in *; lia). rewrite AV2. apply AV1; [exact Hr | unfold sp0 in *; lia].
+ intros a Hp. pose proof Hp as [Hh [b Hb]]. apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). apply Hpres3.
apply (apresent_same H mem1 mem2 a (M2 _)).
rewrite (AE2y.apresent_mod _ mem1 a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [apply (apresent_same H mem mem1 a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem mem1 a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp].
Qed.
End g.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x c n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 c.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hc : 0 <= c < 256.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hx : 0 < x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis Hsrc : src_ok tfibsegs W regs mem x n.
Hypothesis Ham : amem_range x n.
Hypothesis Hra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis Hhull : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Hypothesis Hcv : consts_view tfibsegs 0x10350 0x10370 W mem.
Theorem memchr_icpt_srr : SRr tfibsegs W (cfg_at tfibsegs MCH_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte tfibsegs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs). set (H := w_H W).
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
assert (Hamr : x + n <= 2 ^ 47 - 1) by (pose proof Ham as Ham'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham'; lia).
destruct (first_idx_ex (fun i => match aview tfibsegs H mem (x + i) with Some b => b | None => -1 end) c n ltac:(lia))
as (k & Hk & Hkb & Hka).
assert (FB : first_byte tfibsegs W mem x n c k).
{ split; [exact Hk|]. split.
- intros i Hi. specialize (Hkb i Hi). cbv beta in Hkb. fold H.
destruct (aview tfibsegs H mem (x + i)) as [b|] eqn:Eb.
+ exists b. split; [reflexivity | exact Hkb].
+ exfalso. apply (proj1 (Hsrc (x + i) ltac:(lia))). exact Eb.
- intros Hlt. specialize (Hka Hlt). cbv beta in Hka. fold H.
destruct (aview tfibsegs H mem (x + k)) as [b|] eqn:Eb; [rewrite Hka; reflexivity | lia]. }
assert (HBEF : forall i, 0 <= i < k -> exists b, aview tfibsegs (w_H W) mem (x + i) = Some b /\ b <> c) by apply FB.
assert (HAT : k < n -> aview tfibsegs (w_H W) mem (x + k) = Some c) by apply FB.
assert (HMC : mconsts_view W mem).
{ intros a Ha. apply Hcv. pose proof mc_bounds as [B1 B2]. lia. }
unfold cfg_at. change (w64 MCH_ENTRY) with (Z_to_bv 64 MCH_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 MCH_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB mchr_rodata ly S H mem EE (mchr_rodata_chk ly) (proj1 HAR))].
unfold stkA, MCH_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2144)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply HpresE. subst sp0. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, mchr_rodata, icpt_rodata, ro_region, extent_of_region, MCH_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia]. }
eapply SRr_bind; [apply (icpt_phase_to W EE MCH_REAL _ _ _ _ _ HS0 r_A)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MCH_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MCH_WIN) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MCH_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R9].
apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R18].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK.
rewrite (RD r _ ltac:(rewrite <- Hi; exact HK)). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (cc & Hin & Hc'). apply chunk_is_sound in Hc'. subst cc.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
eapply SRr_bind.
{ apply (mch_tail B LAWS TB ly S W regs mem md (ms_regs ms1) (ms_mem ms1) mat1 x c n k HPRE Hc Hn Hx Hxn Hk HBEF HAT Hsrc Ham Hra Hhull HMC).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. exact eq_refl.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G11.
- rewrite (RD 12%bv (SOff 12 0) R12). cbn [sv_denot]. rewrite EE12, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 9%bv (SOff 12 0) R9). cbn [sv_denot]. rewrite EE12, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 1%bv (SLit MCH_RET) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 (-2128)) R2). cbn [sv_denot]. rewrite EE2. reflexivity.
- rewrite (RD 18%bv (SOff 10 0) R18). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 20%bv (SLit 1) R20). reflexivity.
- exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia)). - exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia)).
- exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)). - exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)). - exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
- exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)). - exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)). - exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)).
- exact MEQ1.
- intros a Ha. unfold MCH_WIN in Ha.
apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold MCH_WIN. lia.
- replace (spZ regs - 8) with (sp0 + -8) by (subst sp0; lia). exact (CK 0%nat 1 (-8) eq_refl).
- replace (spZ regs - 16) with (sp0 + -16) by (subst sp0; lia). exact (CK 1%nat 8 (-16) eq_refl).
- replace (spZ regs - 24) with (sp0 + -24) by (subst sp0; lia). exact (CK 2%nat 9 (-24) eq_refl).
- replace (spZ regs - 32) with (sp0 + -32) by (subst sp0; lia). exact (CK 3%nat 18 (-32) eq_refl).
- replace (spZ regs - 40) with (sp0 + -40) by (subst sp0; lia). exact (CK 4%nat 19 (-40) eq_refl).
- replace (spZ regs - 48) with (sp0 + -48) by (subst sp0; lia). exact (CK 5%nat 20 (-48) eq_refl).
- replace (spZ regs - 56) with (sp0 + -56) by (subst sp0; lia). exact (CK 6%nat 21 (-56) eq_refl). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HKP & HSB & HA10 & HFR & HPR).
apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HAR'|]. split; [exact HKP|]. split; [exact HSB|].
split; [exists k; split; [exact FB | exact HA10]|]. split; [exact HFR | exact HPR].
Qed.
End h.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem memchr_icpt_realizesM : forall B, AR_laws tfibsegs B -> SegBSyms B ->
amemchr_realizesM tfibsegs B 0x10350 0x10370 0x43a3c.
Proof.
intros B LAWS TB ly S W regs mem md x c n HPRE G10 G11 G12 Hc Hn Hx Hxn Hsrc Ham Hra Hhull Hcv.
change 0x43a3c with MCH_ENTRY.
apply (memchr_icpt_srr B LAWS TB ly S W regs mem md x c n); assumption.
Qed.
Theorem memchr_icpt_realizes : forall B, AR_laws tfibsegs B -> SegBSyms B ->
amemchr_realizes tfibsegs B 0x43a3c.
Proof.
intros B LAWS TB ly S W regs mem md x c n HPRE G10 G11 G12 Hc Hn Hx Hxn Hsrc Ham Hra Hhull Hrom.
apply (memchr_icpt_realizesM B LAWS TB ly S W regs mem md x c n HPRE G10 G11 G12 Hc Hn Hx Hxn Hsrc Ham Hra Hhull).
apply (consts_view_of_rom_view tfibsegs 0x10350 0x10370 W mem); [|exact Hrom].
intros a Ha. apply mc_in_rom. pose proof mc_bounds as [B1 B2]. lia.
Qed.
End i.
