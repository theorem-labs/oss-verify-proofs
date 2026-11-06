(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE7d.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE7d.v, with its module names and numbers changed; 527 of its 636 lines of code are new or changed and 367 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI RtSStrcspnDef RtSStrcspnIT.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtSIstrlen RtSStrcspnIY RtSStrcspnIX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The walk of the strcspn interceptor of plugin-hostd/fuzz_command's ASan+UBSan build, from its trampoline
   PC_strcspn = 0x45198 (`j 0x46ce4`) to its return, at the contract RtString.astrcspn_realizes (window 2 * ESTACK),
   in the shape of the strlen interceptor's walk (lib/B/Rt/RtSStrlenWalk.v, RtSStrlen.v). The walk of
   lib/A/Rt/RtSStrcspnIW.v moved by the name-keyed A-to-B address map; measured on the pinned fuzz_command.asan-ubsan
   (its objdump listing at ___interceptor_strcspn), whose code is fuzz_command.asan's modulo pc-relative fields:
     0x46ce4..0x46d14  prologue: frame 2032 + 128 = 2160, ra s0..s8 saved at sp0 - 8 .. sp0 - 80, s0 = sp0
     0x46d20  jal TryAsanInitFromRtl 0x5f68c (s2 = its result, 1); 0x46d24 the REAL slot 0xa7ca0 = 0x9ee10
     0x46d38  jalr a2: musl's strcspn 0x9ee10 (a0 = str, a1 = set, ra 0x46d3c, sp = sp0 - 2160), taken as the
              contract RtSStrcspnDef.amcspn_realizes (Section hypothesis MUSL)
     0x46d3c  beqz s2 (not taken); the flag common_flags + 247 (= 1, not taken); s5 = r; jal internal_strlen 0x69b5c
              on the set (RtSIstrlen.tfib_istrlen)
     0x46d64  the set site (RtSStrcspnIY.siteY_srr, size |set| + 1), the flag + 245 (= 0, not taken)
     0x46dc0  the string site (RtSStrcspnIX.siteX_srr, size r + 1)
     0x46e0c  epilogue, a0 = r, ret.
   Phase A (the trampoline to the REAL call) is one symbolic run; the epilogue another, from a fresh state that
   holds the ten saved words. The deepest window is musl's: 2160 + MCSPN_K = 6352 <= 2 * ESTACK. *)

Definition CI_REAL : Z := 0x9ee10.
Definition CI_RET : Z := 0x46d3c.
Definition CI_ISL : Z := 0x69b5c.
Definition CI_END : Z := 0x46e0c.
Definition CI_FRAME : Z := 2160.
Definition CI_WIN : Z := 2176.
Lemma ci_consts : CI_REAL = MCSPN_ENTRY /\ CI_RET = MCSPN_RA /\ CI_ISL = RtSIstrlen.A_ISL /\
CI_END = RtSStrcspnIX.RCX_END /\ RtSStrcspnIY.RCY_END = RtSStrcspnIX.RCX_ENTRY /\ RtSStrcspnIY.RCY_ENTRY = 0x46d64 /\
MCSPN_K = 4192.
Proof. repeat split; reflexivity. Qed.

(* ---- phase A: the trampoline, the prologue, TryAsanInitFromRtl, the load of the REAL slot ---- *)
Definition ciA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [(0xa7ca0, 8, [(0, 8%N, 0x9ee10)])].
Lemma ciA_rodata_chk : forall ly, rodata_chk ly ciA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- CI_WIN) 0 (- CI_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 (2^47) 0); (11%nat, mkAF 1 (2^47) 0)].
Definition ssA : sstate := mkSS PC_strcspn sr_atoms (stkA :: map ro_region ciA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_ci FUEL CI_REAL s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A : RUNTOR ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
(* ra, s0, s1, ..., s8 are saved at these offsets below the caller's sp *)
Definition SAVEDA : list (Z * Z) :=
[(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72); (24, -80)].
Definition KEPTA : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? CI_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - CI_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 1 (SLit CI_RET) && reg_is ss 2 (SOff 2 (- CI_FRAME)) &&
reg_is ss 8 (SOff 2 0) && reg_is ss 9 (SOff 10 0) && reg_is ss 18 (SLit 1) && reg_is ss 19 (SOff 11 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.

(* ---- phase B: from the return of musl's strcspn to the call of internal_strlen ---- *)
Definition ciB_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0xa5f40, 8, [(0, 8%N, 0x142768)]); (0x142858, 8, [(0, 8%N, 0x101000100000000)])].
Lemma ciB_rodata_chk : forall ly, rodata_chk ly ciB_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition ssB : sstate := mkSS CI_RET sr_atoms (map ro_region ciB_rodata) None (mkFacts [] [] []).

(* ---- the epilogue: sp += 128, the ten saved words come back, sp += 2032, ret ---- *)
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2152 (CVal 8 (SOff 32 0)); YP09.mkChunk 2144 (CVal 8 (SOff 33 0));
YP09.mkChunk 2136 (CVal 8 (SOff 34 0)); YP09.mkChunk 2128 (CVal 8 (SOff 35 0));
YP09.mkChunk 2120 (CVal 8 (SOff 36 0)); YP09.mkChunk 2112 (CVal 8 (SOff 37 0));
YP09.mkChunk 2104 (CVal 8 (SOff 38 0)); YP09.mkChunk 2096 (CVal 8 (SOff 39 0));
YP09.mkChunk 2088 (CVal 8 (SOff 40 0)); YP09.mkChunk 2080 (CVal 8 (SOff 41 0))].
Definition ss_epi : sstate :=
mkSS CI_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 CI_FRAME 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ci FUEL s.
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.

Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); reflexivity. Qed.

Lemma cspn_len_le : forall set s, (PCspn.cspn_len set s <= length s)%nat.
Proof.
intros set s. induction s as [|c s IH]; cbn [PCspn.cspn_len length]; [lia|].
destruct (existsb _ set); lia.
Qed.

Lemma ci_mod8 : forall z c, z mod 16 = 0 -> c mod 8 = 0 -> (z - c) mod 8 = 0.
Proof.
intros z c Hz Hc. pose proof (Z.div_mod z 16 ltac:(lia)) as Dz. pose proof (Z.div_mod c 8 ltac:(lia)) as Dc.
rewrite Hz in Dz. rewrite Hc in Dc. symmetry. apply Z.mod_unique_pos with (q := 2 * (z / 16) - c / 8); lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ci_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_ci FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_ci tbl_ci_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Hypothesis MUSL : amcspn_realizes B MCSPN_ENTRY A_SSP_GOT A_SSP_GUARD.

Section t.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(x y : Z) (str set : list byte).
Hypothesis GRD : aguard_ok tfibsegs W mem A_SSP_GOT A_SSP_GUARD.
Hypothesis HPRE : ecall_pre_stk tfibsegs B (2 * ESTACK) ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 y.
Hypothesis Hx : 0 < x.
Hypothesis Hy : 0 < y.
Hypothesis HSTR : astr_at tfibsegs W mem x str.
Hypothesis HSET : astr_at tfibsegs W mem y set.
Hypothesis HRDX : aread_ok tfibsegs (2 * ESTACK) W regs mem x (astr_len str + 1).
Hypothesis HRDY : aread_ok tfibsegs (2 * ESTACK) W regs mem y (astr_len set + 1).
Hypothesis HTX : atail_vis tfibsegs W mem (x + astr_len str).
Hypothesis HROM : rt_rom_view tfibsegs B W mem.

Local Notation H := (w_H W).
Local Notation sp0 := (spZ regs).
Local Notation RV := (Z.of_nat (PCspn.cspn_len set str)).
Local Notation POST := (art_post tfibsegs B (2 * ESTACK) ly S W regs mem md (fun _ => False)
(fun regs' _ => getr regs' 10 = w64 RV)).

(* the ten words the prologue saves, in the order of SAVEDA *)
Definition SAVED : list word :=
[getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22;
getr regs 23; getr regs 24].

(* what every stage keeps: AR, the bytes outside the window, presence, the window present, the saved words *)
Definition FRM (m : word -> option byte) (mdx : Model) : Prop :=
AR tfibsegs B ly S W m mdx /\ same_but_materialized md mdx /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * ESTACK <= a < sp0) -> aview tfibsegs H m a = aview tfibsegs H mem a) /\
(forall a, apresent H mem a -> apresent H m a) /\
(forall a, sp0 - 2 * ESTACK <= a < sp0 -> apresent H m a) /\
(forall j, (j < 10)%nat -> val_mem tfibsegs (mrestrict H m) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j SAVED (Z_to_bv 64 0)))).

(* the registers no stage writes and the epilogue does not restore *)
Definition KEEP (r : bvmap 5 word) : Prop :=
forall q, In q [3; 4; 25; 26; 27] -> getr r (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).

Lemma ci_basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 2 * ESTACK <= sp0 /\ sp0 mod 16 = 0 /\
ly_stk_lo ly + 2 * ESTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\
x + astr_len str + 1 <= 2 ^ 47 - 1 /\ y + astr_len set + 1 <= 2 ^ 47 - 1 /\
TFIB_IMG_END <= sp0 - 2 * ESTACK /\ kHighShadowEnd <= sp0 - 2 * ESTACK.
Proof.
pose proof HPRE as ((HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & Hslo2 & Hpres2).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof HRDX as (_ & _ & _ & _ & HAMX & _ & _). pose proof HRDY as (_ & _ & _ & _ & HAMY & _ & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, TFIB_IMG_END, ESTACK in *.
repeat split; lia.
Qed.

(* the bytes of the two strings lie outside the window *)
Lemma ci_out : (forall a, x <= a < x + astr_len str + 1 -> ~ (sp0 - 2 * ESTACK <= a < sp0)) /\
(forall a, y <= a < y + astr_len set + 1 -> ~ (sp0 - 2 * ESTACK <= a < sp0)).
Proof.
pose proof HRDX as (_ & _ & _ & HX & _ & _ & _). pose proof HRDY as (_ & _ & _ & HY & _ & _ & _).
split; intros a Ha; [exact (proj2 (HX a ltac:(lia))) | exact (proj2 (HY a ltac:(lia)))].
Qed.

Lemma FRM_ext : forall m m' mdx mdx', FRM m mdx -> (forall z, m' z = m z) -> same_but_materialized mdx mdx' -> FRM m' mdx'.
Proof.
intros m m' mdx mdx' (HAR & Hsbm & AV & PR & PW & SV) MEQ Hsbm'.
assert (AVe : forall a, aview tfibsegs H m' a = aview tfibsegs H m a) by (intros a; apply aview_same; apply MEQ).
split; [exact (ar_same B LAWS ly S W m mdx m' mdx' HAR MEQ Hsbm')|].
split; [exact (same_but_materialized_trans _ _ _ Hsbm Hsbm')|].
split; [intros a Hr Hw; rewrite AVe; exact (AV a Hr Hw)|].
split; [intros a Ha; apply (apresent_same H m m' a (MEQ _)); exact (PR a Ha)|].
split; [intros a Ha; apply (apresent_same H m m' a (MEQ _)); exact (PW a Ha)|].
intros j Hj. apply (YF0x.val_mem_ext (mrestrict H m)); [|exact (SV j Hj)].
intros k Hk. apply mbyte_of_aview. apply AVe.
Qed.

(* a call that writes only [lo, hi), inside the window and below the saved words *)
Lemma FRM_step : forall m m' mdx mdx' lo hi, FRM m mdx ->
AR tfibsegs B ly S W m' mdx' -> same_but_materialized mdx mdx' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
(forall a, apresent H m a -> apresent H m' a) ->
sp0 - 2 * ESTACK <= lo -> hi <= sp0 - 80 ->
FRM m' mdx'.
Proof.
intros m m' mdx mdx' lo hi (HAR & Hsbm & AV & PR & PW & SV) HAR' Hsbm' AV' PR' Hlo Hhi.
pose proof ci_basics as (Bsp & _). assert (HES : ESTACK = 4096) by reflexivity.
split; [exact HAR'|].
split; [exact (same_but_materialized_trans _ _ _ Hsbm Hsbm')|].
split; [intros a Hr Hw; rewrite (AV' a Hr) by lia; exact (AV a Hr Hw)|].
split; [intros a Ha; exact (PR' a (PR a Ha))|].
split; [intros a Ha; exact (PR' a (PW a Ha))|].
intros j Hj. apply (YF0x.val_mem_ext (mrestrict H m)); [|exact (SV j Hj)].
intros k Hk. apply mbyte_of_aview. apply AV'; lia.
Qed.

Lemma ci_rom : forall m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * ESTACK <= a < sp0) -> aview tfibsegs H m a = aview tfibsegs H mem a) ->
rt_rom_view tfibsegs B W m.
Proof.
intros m AV. pose proof ci_basics as (Bsp & _ & _ & _ & _ & _ & _ & Bimg & _). assert (HES : ESTACK = 4096) by reflexivity.
apply (rt_rom_view_view B W mem m (sp0 - 2 * ESTACK) Bimg); [|exact HROM].
intros a Ha. apply AV; lia.
Qed.

(* ---- the epilogue (as RtSStrlenWalk.v:306-405) ---- *)
Lemma ci_epi : forall regs5 mem5 md5, FRM mem5 md5 -> KEEP regs5 -> spZ regs5 = sp0 - CI_FRAME -> getr regs5 10 = w64 RV ->
SRr tfibsegs W (cfg_at tfibsegs CI_END regs5 mem5 md5) POST.
Proof.
intros regs5 mem5 md5 (HAR5 & Hsbm5 & AV5 & PR5 & PW5 & SV5) K5 Rsp5 A5.
pose proof HPRE as ((HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & Hslo2 & Hpres2).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & _). assert (HES : ESTACK = 4096) by reflexivity.
pose proof YF0x.Hwx_tfa as Hwx. unfold CI_FRAME in *.
set (E4 := Ereg regs5 SAVED).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2160).
{ subst E4. rewrite (ew_Ereg_nat regs5 _ 2 2%bv eq_refl). exact Rsp5. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs5 (w64 CI_END) mem5 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs5 SAVED) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. unfold CI_FRAME.
replace (base_val E4 (Some 2%nat)) with (sp0 - 2160) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) off, off = 2152 - 8 * Z.of_nat j -> (j < 10)%nat ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem5) (sp0 - 2160) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off Hoff Hj. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2160) off 8 _ (bv_unsigned (nth j SAVED (Z_to_bv 64 0)))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs5 _ j), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (nth j SAVED (Z_to_bv 64 0))). zside.
- zside.
- subst off. replace (sp0 - 2160 + (2152 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact (SV5 j Hj). }
repeat apply Forall_cons; try apply Forall_nil.
+ exact (CK 0%nat 2152 eq_refl ltac:(lia)).
+ exact (CK 1%nat 2144 eq_refl ltac:(lia)).
+ exact (CK 2%nat 2136 eq_refl ltac:(lia)).
+ exact (CK 3%nat 2128 eq_refl ltac:(lia)).
+ exact (CK 4%nat 2120 eq_refl ltac:(lia)).
+ exact (CK 5%nat 2112 eq_refl ltac:(lia)).
+ exact (CK 6%nat 2104 eq_refl ltac:(lia)).
+ exact (CK 7%nat 2096 eq_refl ltac:(lia)).
+ exact (CK 8%nat 2088 eq_refl ltac:(lia)).
+ exact (CK 9%nat 2080 eq_refl ltac:(lia)).
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. repeat split; try lia.
replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Bal. }
eapply SRr_bind; [apply (ci_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_ci tbl_ci_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem5 z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22.
rreg HS4 (23%bv : bv 5) Q23. rreg HS4 (24%bv : bv 5) Q24.
rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X : forall j, ew E4 (32 + j) = nth j SAVED (Z_to_bv 64 0)) by (intros j; subst E4; exact (ew_Ereg_extra regs5 _ j)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs5 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs5 _ ii rr Hnth)).
assert (KK : forall q (rr : bv 5), rr = Z_to_bv 5 q -> In q [3; 4; 25; 26; 27] -> getr regs5 rr = getr regs rr).
{ intros q rr -> Hq. exact (K5 q Hq). }
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; change (ew E4 32) with (ew E4 (32 + 0)); rewrite (X 0%nat); cbn [nth SAVED]; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md5) mat' md5).
pose proof (same_but_materialized_frame md5 _ (with_vm_backing_same md5 mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem5 a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
- apply (al_frame _ _ LAWS ly S W mem5 md5 (ms_mem ms4) _ HAR5).
+ intros a Hr Hown. apply AV4.
+ intros a Hv. rewrite AV4. exact Hv.
+ apply MF. + apply MF. + apply MF.
+ exact (YE2y.hs_kept_eq _ _ _ MEQ4).
- intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2.
unfold spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64). pose proof (u64_range (getr regs 2)). unfold spZ in *. rewrite Z.mod_small by lia. lia.
+ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl). exact (KK 3 3%bv ltac:(apply bv_eq; reflexivity) ltac:(cbn; lia)).
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl). exact (KK 4 4%bv ltac:(apply bv_eq; reflexivity) ltac:(cbn; lia)).
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat).
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat).
+ replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat).
+ replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat).
+ replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat).
+ replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat).
+ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 7%nat).
+ replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 8%nat).
+ replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24. exact (X 9%nat).
+ replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl). exact (KK 25 25%bv ltac:(apply bv_eq; reflexivity) ltac:(cbn; lia)).
+ replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl). exact (KK 26 26%bv ltac:(apply bv_eq; reflexivity) ltac:(cbn; lia)).
+ replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl). exact (KK 27 27%bv ltac:(apply bv_eq; reflexivity) ltac:(cbn; lia)).
- eapply same_but_materialized_trans; [exact Hsbm5 | apply with_vm_backing_same].
- rewrite Q10, (Y 10%nat 10%bv eq_refl). exact A5.
- intros a Hr Hs _. rewrite AV4. apply AV5; [exact Hr|]. unfold ascratch_stk in Hs. exact Hs.
- intros a Hp. apply (apresent_same H mem5 (ms_mem ms4) a (MEQ4 _)). exact (PR5 a Hp).
- intros a Ha. apply (apresent_same H mem5 (ms_mem ms4) a (MEQ4 _)). apply PW5. unfold ascratch_stk in Ha. exact Ha.
Qed.

(* the string's prefix of r + 1 bytes is readable at the string site *)
Lemma ci_rdx : forall regs4 mem4, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * ESTACK <= a < sp0) -> aview tfibsegs H mem4 a = aview tfibsegs H mem a) ->
spZ regs4 = sp0 - CI_FRAME ->
aread_ok tfibsegs RtSStrcspnIX.RC_SCR W regs4 mem4 x (RV + 1).
Proof.
intros regs4 mem4 AV4 Rsp4.
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity. pose proof ci_out as (Ox & Oy).
pose proof (cspn_len_le set str) as Hle. unfold astr_len in *.
apply (aread_ok_kept (2 * ESTACK) RtSStrcspnIX.RC_SCR W regs regs4 mem mem4 (sp0 - 2 * ESTACK) sp0 x (RV + 1)).
- intros a Hr Hw. exact (AV4 a Hr Hw).
- apply (aread_ok_prefix (2 * ESTACK) W regs mem x (Z.of_nat (length str) + 1)); [exact HRDX | lia].
- intros a Ha. apply Ox. lia.
- exact Bsh.
- lia.
- intros a Ha. rewrite Rsp4. unfold RtSStrcspnIX.RC_SCR, CI_FRAME, ESTACK in *. intros Hw. apply (Ox a ltac:(lia)). lia.
Qed.

Lemma ci_rdy : forall regs3 mem3, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * ESTACK <= a < sp0) -> aview tfibsegs H mem3 a = aview tfibsegs H mem a) ->
spZ regs3 = sp0 - CI_FRAME ->
aread_ok tfibsegs RtSStrcspnIY.RC_SCR W regs3 mem3 y (astr_len set + 1).
Proof.
intros regs3 mem3 AV3 Rsp3.
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity. pose proof ci_out as (Ox & Oy).
apply (aread_ok_kept (2 * ESTACK) RtSStrcspnIY.RC_SCR W regs regs3 mem mem3 (sp0 - 2 * ESTACK) sp0 y (astr_len set + 1)).
- intros a Hr Hw. exact (AV3 a Hr Hw).
- exact HRDY.
- intros a Ha. apply Oy. lia.
- exact Bsh.
- lia.
- intros a Ha. rewrite Rsp3. unfold RtSStrcspnIY.RC_SCR, CI_FRAME, ESTACK in *. intros Hw. apply (Oy a ltac:(lia)). lia.
Qed.

(* ---- the string site, 0x46dc0 -> 0x46e0c ---- *)
Lemma ci_s2 : forall regs4 mem4 md4, FRM mem4 md4 -> KEEP regs4 -> spZ regs4 = sp0 - CI_FRAME ->
getr regs4 10 = w64 RV -> getr regs4 19 = w64 RV -> getr regs4 21 = w64 RV -> getr regs4 9 = w64 x ->
SRr tfibsegs W (cfg_at tfibsegs RtSStrcspnIX.RCX_ENTRY regs4 mem4 md4) POST.
Proof.
intros regs4 mem4 md4 F4 K4 Rsp4 A10 A19 A21 A9.
pose proof F4 as (HAR4 & Hsbm4 & AV4 & PR4 & PW4 & SV4).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity.
pose proof (cspn_len_le set str) as Hle.
eapply SRr_bind.
{ apply (RtSStrcspnIX.siteX_srr B LAWS TB ly S W regs4 mem4 md4 x (RV + 1) RV).
- exact HAR4.
- rewrite Rsp4. unfold CI_FRAME. replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Bal.
- rewrite Rsp4. unfold RtSStrcspnIX.RC_SCR, CI_FRAME, ESTACK in *. lia.
- rewrite Rsp4. unfold CI_FRAME. lia.
- intros a Ha. rewrite Rsp4 in Ha. apply PW4. unfold RtSStrcspnIX.RC_SCR, CI_FRAME, ESTACK in *. lia.
- rewrite A19. unfold w64. f_equal. lia.
- exact A9.
- exact A21.
- exact A10.
- lia.
- exact Hx.
- exact (ci_rdx regs4 mem4 AV4 Rsp4).
- exact (ci_rom mem4 AV4). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HAR5 & KP5 & Hsbm5 & A5 & Hfr5 & Hpres5).
apply (ci_epi regs5 mem5 md5).
- apply (FRM_step mem4 mem5 md4 md5 (sp0 - CI_FRAME - 72) (sp0 - CI_FRAME) F4 HAR5 Hsbm5); [| exact Hpres5 | unfold CI_FRAME, ESTACK; lia | unfold CI_FRAME; lia].
intros a Hr Hw. apply Hfr5; [exact Hr|]. rewrite Rsp4. unfold RtSStrcspnIX.RC_SCR. exact Hw.
- intros q Hq. rewrite KP5; [exact (K4 q Hq) | | | |]; cbn in Hq; unfold acallee_saved; lia.
- transitivity (spZ regs4); [unfold spZ; f_equal; exact (KP5 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Rsp4].
- exact A5.
Qed.

(* ---- the set site, 0x46d64 -> 0x46dc0 ---- *)
Lemma ci_s1 : forall regs3 mem3 md3, FRM mem3 md3 -> KEEP regs3 -> spZ regs3 = sp0 - CI_FRAME ->
getr regs3 10 = w64 (astr_len set) -> getr regs3 19 = w64 y -> getr regs3 21 = w64 RV ->
getr regs3 23 = w64 0x142768 -> getr regs3 9 = w64 x ->
SRr tfibsegs W (cfg_at tfibsegs RtSStrcspnIY.RCY_ENTRY regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 F3 K3 Rsp3 A10 A19 A21 A23 A9.
pose proof F3 as (HAR3 & Hsbm3 & AV3 & PR3 & PW3 & SV3).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ apply (RtSStrcspnIY.siteY_srr B LAWS TB ly S W regs3 mem3 md3 y (astr_len set + 1) RV).
- exact HAR3.
- rewrite Rsp3. unfold CI_FRAME. replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Bal.
- rewrite Rsp3. unfold RtSStrcspnIY.RC_SCR, CI_FRAME, ESTACK in *. lia.
- rewrite Rsp3. unfold CI_FRAME. lia.
- intros a Ha. rewrite Rsp3 in Ha. apply PW3. unfold RtSStrcspnIY.RC_SCR, CI_FRAME, ESTACK in *. lia.
- rewrite A10. unfold w64. f_equal. lia.
- exact A19.
- exact A21.
- exact A23.
- unfold astr_len. lia.
- exact Hy.
- exact (ci_rdy regs3 mem3 AV3 Rsp3).
- exact (ci_rom mem3 AV3). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & KP4 & Hsbm4 & A4 & B4 & Hfr4 & Hpres4).
change (cfg_at tfibsegs RtSStrcspnIY.RCY_END regs4 mem4 md4) with (cfg_at tfibsegs RtSStrcspnIX.RCX_ENTRY regs4 mem4 md4).
apply (ci_s2 regs4 mem4 md4).
- apply (FRM_step mem3 mem4 md3 md4 (sp0 - CI_FRAME - 72) (sp0 - CI_FRAME) F3 HAR4 Hsbm4); [| exact Hpres4 | unfold CI_FRAME, ESTACK; lia | unfold CI_FRAME; lia].
intros a Hr Hw. apply Hfr4; [exact Hr|]. rewrite Rsp3. unfold RtSStrcspnIY.RC_SCR. exact Hw.
- intros q Hq. rewrite KP4; [exact (K3 q Hq) | | |]; cbn in Hq; unfold acallee_saved; lia.
- transitivity (spZ regs3); [unfold spZ; f_equal; exact (KP4 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact Rsp3].
- exact A4.
- exact B4.
- transitivity (getr regs3 21); [exact (KP4 21 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact A21].
- transitivity (getr regs3 9); [exact (KP4 9 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact A9].
Qed.

(* ---- phase B and internal_strlen, 0x46d3c -> 0x46d64 ---- *)
Lemma ci_B : forall regs2 mem2 md2, FRM mem2 md2 -> KEEP regs2 -> spZ regs2 = sp0 - CI_FRAME ->
getr regs2 18 = w64 1 -> getr regs2 10 = w64 RV -> getr regs2 19 = w64 y -> getr regs2 9 = w64 x ->
SRr tfibsegs W (cfg_at tfibsegs CI_RET regs2 mem2 md2) POST.
Proof.
intros regs2 mem2 md2 F2 K2 Rsp2 A18 A10 A19 A9.
pose proof F2 as (HAR2 & Hsbm2 & AV2 & PR2 & PW2 & SV2).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity. pose proof ci_out as (Ox & Oy).
pose proof YF0x.Hwx_tfa as Hwx.
set (EE := YE2y.Env regs2 []).
assert (EEreg : forall i (q : bv 5), Z.of_nat i = bv_unsigned q -> ew EE i = getr regs2 q) by (intros; apply YE2y.Env_reg; assumption).
assert (E18 : ew EE 18 = Z_to_bv 64 1) by (rewrite (EEreg 18%nat 18%bv eq_refl); exact A18).
assert (HS0 : st_ok tfibsegs EE ssB (restrict H (mkst regs2 (Z_to_bv 64 CI_RET) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssB, EE, YE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- exact (rodata_ok B TB ciB_rodata ly S H mem2 EE (ciB_rodata_chk ly) (proj1 HAR2)).
- apply pairwise_disjoint_of_extents. unfold ciB_rodata, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N zpairwise_disjoint zall_disjoint].
unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 CI_RET) with (Z_to_bv 64 CI_RET).
pose proof (same_but_materialized_refl md2) as HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_atom_eq0 EE 18 1 E18) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 CI_ISL. ro_mem MEQ. newmd HMD.
lazymatch type of HS0 with st_ok _ _ _ (restrict _ ?m) => rename m into msI end.
rreg HS0 (1%bv : bv 5) R1. rreg HS0 (2%bv : bv 5) R2. rreg HS0 (9%bv : bv 5) R9. rreg HS0 (10%bv : bv 5) R10.
rreg HS0 (19%bv : bv 5) R19. rreg HS0 (21%bv : bv 5) R21. rreg HS0 (23%bv : bv 5) R23.
rreg HS0 (3%bv : bv 5) R3. rreg HS0 (4%bv : bv 5) R4. rreg HS0 (25%bv : bv 5) R25. rreg HS0 (26%bv : bv 5) R26. rreg HS0 (27%bv : bv 5) R27.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS0 eq_refl) as Hshape. cbn [ss_pc] in Hshape. rewrite Hshape.
(* the set, at the memory of the call *)
assert (AVI : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * ESTACK <= a < sp0) -> aview tfibsegs H (ms_mem msI) a = aview tfibsegs H mem a)
by (intros a Hr Hw; rewrite MEQ; exact (AV2 a Hr Hw)).
assert (HSETI : astr_at tfibsegs W (ms_mem msI) y set).
{ apply (astr_at_kept W mem (ms_mem msI) (sp0 - 2 * ESTACK) sp0 y set); [exact AVI | exact HSET | lia | unfold astr_len in *; lia |].
intros a Ha. exact (Oy a Ha). }
destruct HSETI as (HBI & HNZ).
destruct (RtSIstrlen.tfib_istrlen set (w64 y) (mrestrict H (ms_mem msI)) (seg_rom tfibsegs) (ms_regs msI)) as (regs3 & Hms & I10 & IK).
- rewrite R10, (EEreg 19%nat 19%bv eq_refl). exact A19.
- exact HNZ.
- intros j Hj. unfold w64. rewrite unsigned_lit_small by (unfold astr_len in *; lia).
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
rewrite (YF0x.aview_byte H (ms_mem msI) _ _ (HBI j ltac:(rewrite length_app; cbn [length]; lia))).
rewrite Z_to_bv_bv_unsigned. reflexivity.
- unfold w64, astr_len in *. rewrite unsigned_lit_small by lia. lia.
- eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm' _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom].
set (mem3 := munrestrict H (ms_mem msI) (mrestrict H (ms_mem msI))).
assert (M3 : forall z, mem3 z = ms_mem msI z) by (intros z; subst mem3; apply munrestrict_mrestrict_same).
assert (IKr : forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr regs3 r = getr (ms_regs msI) r) by (intros r; apply IK).
replace (v_jalr (getr (ms_regs msI) 1) 0) with (w64 RtSStrcspnIY.RCY_ENTRY) by (rewrite R1; apply bv_eq; vm_compute; reflexivity).
change (mkCfg (mkst regs3 (w64 RtSStrcspnIY.RCY_ENTRY) mem3 (seg_rom tfibsegs)) model')
with (cfg_at tfibsegs RtSStrcspnIY.RCY_ENTRY regs3 mem3 model').
apply (ci_s1 regs3 mem3 model').
+ apply (FRM_ext mem2 mem3 md2 model' F2); [intros z; rewrite M3, MEQ; reflexivity|].
exact (same_but_materialized_trans _ _ _ HMD Hsbm').
+ intros q Hq. cbn in Hq.
destruct Hq as [<- | [<- | [<- | [<- | [<- | []]]]]].
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite IKr by (intros Hc; discriminate Hc).
rewrite R3, (EEreg 3%nat 3%bv eq_refl). exact (K2 3 ltac:(cbn; lia)).
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite IKr by (intros Hc; discriminate Hc).
rewrite R4, (EEreg 4%nat 4%bv eq_refl). exact (K2 4 ltac:(cbn; lia)).
* replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite IKr by (intros Hc; discriminate Hc).
rewrite R25, (EEreg 25%nat 25%bv eq_refl). exact (K2 25 ltac:(cbn; lia)).
* replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite IKr by (intros Hc; discriminate Hc).
rewrite R26, (EEreg 26%nat 26%bv eq_refl). exact (K2 26 ltac:(cbn; lia)).
* replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite IKr by (intros Hc; discriminate Hc).
rewrite R27, (EEreg 27%nat 27%bv eq_refl). exact (K2 27 ltac:(cbn; lia)).
+ unfold spZ. rewrite IKr by (intros Hc; discriminate Hc). rewrite R2, (EEreg 2%nat 2%bv eq_refl). exact Rsp2.
+ rewrite I10. reflexivity.
+ rewrite IKr by (intros Hc; discriminate Hc). rewrite R19, (EEreg 19%nat 19%bv eq_refl). exact A19.
+ rewrite IKr by (intros Hc; discriminate Hc). rewrite R21, (EEreg 10%nat 10%bv eq_refl). exact A10.
+ rewrite IKr by (intros Hc; discriminate Hc). rewrite R23. reflexivity.
+ rewrite IKr by (intros Hc; discriminate Hc). rewrite R9, (EEreg 9%nat 9%bv eq_refl). exact A9.
Qed.

(* ---- the call of musl's strcspn, under its contract MUSL, at sp0 - 2160 ---- *)
Lemma ci_M : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1,
getr regs1 10 = w64 x -> getr regs1 11 = w64 y -> getr regs1 1 = w64 CI_RET -> getr regs1 2 = w64 (sp0 - CI_FRAME) ->
getr regs1 18 = w64 1 -> getr regs1 19 = w64 y -> getr regs1 9 = w64 x -> KEEP regs1 ->
(forall z : word, ~ (sp0 - CI_WIN <= bv_unsigned z < sp0) -> mem1 z = mem z) ->
(forall a, sp0 - CI_WIN <= a < sp0 -> apresent H mem1 a) ->
(forall j, (j < 10)%nat -> val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j SAVED (Z_to_bv 64 0)))) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 CI_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md)) POST.
Proof.
intros regs1 mem1 mat1 A10 A11 A1 A2 A18 A19 A9 K1 MEQ1 PW1 SV1.
pose proof HPRE as ((HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & Hslo2 & Hpres2).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity. pose proof ci_out as (Ox & Oy).
unfold astr_len in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (Hsbm1 : same_but_materialized md md1) by apply with_vm_backing_same.
assert (Rsp1 : spZ regs1 = sp0 - CI_FRAME) by (unfold spZ at 1; rewrite A2; unfold w64, CI_FRAME; apply unsigned_lit_small; lia).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CI_WIN <= a < sp0) -> aview tfibsegs H mem1 a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CI_WIN <= a < sp0) -> apresent H mem a -> apresent H mem1 a).
{ intros a Hr Ha Hp. apply (apresent_same H mem mem1 a); [apply MEQ1; rewrite unsigned_lit_small by lia; exact Ha | exact Hp]. }
assert (HAR1 : AR tfibsegs B ly S W mem1 md1).
{ apply (ar_win B LAWS ly S W mem md mem1 md1 (sp0 - CI_WIN) sp0 HAR Hsbm1); unfold CI_WIN, ESTACK in *; try lia; [exact MEQ1 | | exact PW1].
intros a Ha. apply HpresE. lia. }
assert (KO1 : kept_out (aview tfibsegs H mem) (aview tfibsegs H mem1) (sp0 - 2 * ESTACK) sp0).
{ intros a Hr Hw. apply AV1; [exact Hr|]. unfold CI_WIN, ESTACK in *. lia. }
(* the frame for every stage after the call *)
assert (F1 : FRM mem1 md1).
{ split; [exact HAR1|]. split; [exact Hsbm1|]. split; [exact KO1|].
split; [intros a Hp; rewrite (YE2y.apresent_mod _ mem1 a); rewrite (YE2y.apresent_mod _ mem a) in Hp;
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia); set (a' := a mod 2 ^ 64) in *;
destruct (Z_lt_le_dec a' (sp0 - CI_WIN)) as [L1|L1]; [exact (PR1 a' Hr ltac:(lia) Hp)|];
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [exact (PW1 a' ltac:(lia)) | exact (PR1 a' Hr ltac:(lia) Hp)]|].
split; [intros a Ha; destruct (Z_lt_le_dec a (sp0 - CI_WIN)) as [L1|L1];
[apply (PR1 a ltac:(lia) ltac:(lia)); apply Hpres2; unfold ascratch_stk; lia | apply PW1; lia]|].
exact SV1. }
pose proof F1 as (_ & _ & _ & _ & PWF1 & _).
change (mkCfg (mkst regs1 (Z_to_bv 64 CI_REAL) mem1 (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs MCSPN_ENTRY regs1 mem1 md1).
eapply SRr_bind.
{ apply (MUSL ly S W regs1 mem1 md1 x y str set).
- apply (aguard_ok_kept W mem mem1 (sp0 - CI_WIN) sp0 A_SSP_GOT A_SSP_GUARD); [|exact GRD | | | | | ];
unfold A_SSP_GOT, A_SSP_GUARD, CI_WIN in *; try lia.
intros a Hr Hw. exact (AV1 a Hr Hw).
- split; [split; [exact HAR1|] |].
+ split; [rewrite A1; apply ret_ok_lit; [unfold CI_RET; lia | reflexivity]|].
split; [rewrite Rsp1; unfold CI_FRAME; replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia; rewrite Z_mod_plus_full; exact Bal|].
split; [rewrite Rsp1; unfold CI_FRAME, ESTACK in *; lia|].
split; [rewrite Rsp1; unfold CI_FRAME; lia|].
split; [intros a Ha; rewrite Rsp1 in Ha; apply PWF1; unfold CI_FRAME, ESTACK in *; lia|].
split; [transitivity (getr regs 3); [exact (K1 3 ltac:(cbn; lia)) | exact Hgp] | transitivity (getr regs 4); [exact (K1 4 ltac:(cbn; lia)) | exact Htp]].
+ split; [rewrite Rsp1; unfold CI_FRAME, MCSPN_K, ESTACK in *; lia|].
intros a Ha. unfold ascratch_stk in Ha. rewrite Rsp1 in Ha. apply PWF1.
unfold CI_FRAME, MCSPN_K, ESTACK in *; lia.
- exact A10.
- exact A11.
- exact Hx.
- exact Hy.
- apply (astr_at_kept W mem mem1 (sp0 - 2 * ESTACK) sp0 x str KO1 HSTR); [lia | unfold astr_len in *; lia | exact Ox].
- apply (astr_at_kept W mem mem1 (sp0 - 2 * ESTACK) sp0 y set KO1 HSET); [lia | unfold astr_len in *; lia | exact Oy].
- apply (aread_ok_kept (2 * ESTACK) MCSPN_K W regs regs1 mem mem1 (sp0 - 2 * ESTACK) sp0 x (Z.of_nat (length str) + 1) KO1 HRDX);
[intros a Ha; apply Ox; lia | exact Bsh | lia |]. intros a Ha. rewrite Rsp1. intros Hw. apply (Ox a ltac:(lia)). unfold CI_FRAME, MCSPN_K, ESTACK in *. lia.
- apply (aread_ok_kept (2 * ESTACK) MCSPN_K W regs regs1 mem mem1 (sp0 - 2 * ESTACK) sp0 y (Z.of_nat (length set) + 1) KO1 HRDY);
[intros a Ha; apply Oy; lia | exact Bsh | lia |]. intros a Ha. rewrite Rsp1. intros Hw. apply (Oy a ltac:(lia)). unfold CI_FRAME, MCSPN_K, ESTACK in *. lia.
- apply (atail_vis_kept W mem mem1 (sp0 - 2 * ESTACK) sp0 (x + Z.of_nat (length str)) KO1 HTX); [lia | |].
+ pose proof (Z.mod_pos_bound (x + Z.of_nat (length str)) 8 ltac:(lia)). lia.
+ apply (tail_out_win (x + Z.of_nat (length str)) (sp0 - 2 * ESTACK) sp0).
* apply ci_mod8; [exact Bal | reflexivity].
* rewrite <- (Z.sub_0_r sp0). apply ci_mod8; [exact Bal | reflexivity].
* apply Ox. lia.
- exact (ci_rom mem1 KO1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & A2' & Hfr2 & Hpres2' & Hscr2).
assert (Hra1 : raZ regs1 = CI_RET) by (unfold raZ; rewrite A1; unfold w64, CI_RET; apply unsigned_lit_small; lia).
rewrite Hra1.
apply (ci_B regs2 mem2 md2).
- apply (FRM_step mem1 mem2 md1 md2 (sp0 - CI_FRAME - MCSPN_K) (sp0 - CI_FRAME) F1 HAR2 Hsbm2); [| exact Hpres2' | unfold CI_FRAME, MCSPN_K, ESTACK; lia | unfold CI_FRAME; lia].
intros a Hr Hw. apply Hfr2; [exact Hr | | tauto]. unfold ascratch_stk. rewrite Rsp1. exact Hw.
- intros q Hq. rewrite HP2; [exact (K1 q Hq)|]. cbn in Hq. unfold acallee_saved. lia.
- transitivity (spZ regs1); [unfold spZ; f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact Rsp1].
- transitivity (getr regs1 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact A18].
- exact A2'.
- transitivity (getr regs1 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact A19].
- transitivity (getr regs1 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact A9].
Qed.

(* ---- phase A, from the trampoline (as RtSStrlenWalk.v:408-513) ---- *)
Lemma ci_main : SRr tfibsegs W (cfg_at tfibsegs PC_strcspn regs mem md) POST.
Proof using All.
pose proof HPRE as ((HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & Hslo2 & Hpres2).
pose proof ci_basics as (Bsp & Bhi & Bal & Bslo & Bshi & Bx & By & Bimg & Bsh). assert (HES : ESTACK = 4096) by reflexivity.
unfold astr_len in *.
unfold cfg_at. change (w64 PC_strcspn) with (Z_to_bv 64 PC_strcspn).
set (EE := YE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 PC_strcspn) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB ciA_rodata ly S H mem EE (ciA_rodata_chk ly) (proj1 HAR))].
unfold stkA, CI_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2176)); [exact EE2 | lia | lia |].
intros a Ha. apply YF0x.apresent_writable; [unfold TFIB_IMG_END, kHighMemBeg, ESTACK in *; lia|]. apply HpresE. unfold ESTACK. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, ciA_rodata, icpt_rodata, ro_region, extent_of_region, CI_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg, ESTACK in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | lia]. }
eapply (SRr_run_to_gen tfibsegs tbl_ci tbl_ci_ok YF0x.Hwx_tfa W FUEL CI_REAL EE ssA eA RS_running _ md _ HS0 r_A).
intros ms1 mat1 HS1 HF1 HFr1.
assert (MEQ1 : forall z : word, ~ (sp0 - CI_WIN <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- CI_WIN) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold CI_WIN in *. lia. }
clear HF1 HFr1.
(* the state at the call, read off shapeA *)
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK].
apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Smem].
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
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
apply (ci_M (ms_regs ms1) (ms_mem ms1) mat1).
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 11%bv (SOff 11 0) R11). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 1%bv (SLit CI_RET) R1). reflexivity.
- rewrite (RD 2%bv (SOff 2 (- CI_FRAME)) R2). cbn [sv_denot]. rewrite EE2. reflexivity.
- rewrite (RD 18%bv (SLit 1) R18). reflexivity.
- rewrite (RD 19%bv (SOff 11 0) R19). cbn [sv_denot]. rewrite EE11, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- rewrite (RD 9%bv (SOff 10 0) R9). cbn [sv_denot]. rewrite EE10, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- intros q Hq. cbn in Hq. destruct Hq as [<- | [<- | [<- | [<- | [<- | []]]]]].
+ exact (RK (Z_to_bv 5 3) 3%nat eq_refl ltac:(cbn; lia)).
+ exact (RK (Z_to_bv 5 4) 4%nat eq_refl ltac:(cbn; lia)).
+ exact (RK (Z_to_bv 5 25) 25%nat eq_refl ltac:(cbn; lia)).
+ exact (RK (Z_to_bv 5 26) 26%nat eq_refl ltac:(cbn; lia)).
+ exact (RK (Z_to_bv 5 27) 27%nat eq_refl ltac:(cbn; lia)).
- exact MEQ1.
- intros a Ha.
apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, CI_WIN, kHighMemBeg, ESTACK in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold CI_WIN in *. lia.
- intros j Hj.
do 10 (destruct j as [|j]; [
match goal with |- context [sp0 - 8 - 8 * Z.of_nat ?k] =>
let o := eval vm_compute in (- 8 - 8 * Z.of_nat k) in
let rz := eval vm_compute in (fst (nth k SAVEDA (0, 0))) in
replace (sp0 - 8 - 8 * Z.of_nat k) with (sp0 + o) by lia; exact (CK k rz o eq_refl) end |]).
lia.
Qed.

End t.

Theorem cmd_strcspn_icpt : astrcspn_realizes tfibsegs B PC_strcspn A_SSP_GOT A_SSP_GUARD.
Proof.
intros ly S W regs mem md x y str set GRD HPRE G10 G11 Hx Hy HSTR HSET HRDX _ HRDY _ HTX HTY HROM.
exact (ci_main ly S W regs mem md x y str set GRD HPRE G10 G11 Hx Hy HSTR HSET HRDX HRDY HTX HROM).
Qed.

End g.
End d.
