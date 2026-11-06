(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24: no function proved here alone; this is segment S0 of LLVMFuzzerTestOneInput's walk, whose top claim is
   lib/A/PPgMain.v.

   SEGMENT S0 ENTRY, pc 0x806b4 .. 0x807cc, ending at ss_H (0x807d0, lib/A/PPgMainSt.v). Every address was read from
   the pinned image bytes with capstone 5.0.7. The walk, with knock's line it follows:
   - 0x806b4-0x806f4: the 128-byte save frame (13 saves at [sp0-104, sp0)), s0 = sp0, `andi sp,sp,-0x20`; the first
     run stops at 0x806f8 (knock 0x7ef14); sp1 := 32 * ((sp0 - 128) / 32) into env slot 70 (knock -192).
   - the stack region is trimmed to the saves [sp0-104, sp0) (as knock), and region 70 = [s1+16, s1+24) is added
     for the one spill `sd s8,0x10(s1)` at 0x80758 (knock [16,88)).
   - 0x806f8-0x80724: the two GOT loads (0x99050 shadow base, 0x990a8 use-after-return option), s6 := SB, the
     option test `beqz a2` at 0x8071c decided by the option cell's SLit 1, a0 := 0x60, `jal 3ca58` at 0x80724
     (__asan_stack_malloc_1, class 1); the run stops at 0x3ca58 by SR_fetch.
   - the side-stack call through aj_stack_malloc_atS (lib/A/PPgMainCall.v) with class 1 and ASM1; its premise
     count_cid 1 (frames S) < fs_frames 1 is the call-site lemma pin_fs1_site.
   - the class-1 frame facts (F = frame_addr ly 1 fpos, 128 bytes, 16 shadow bytes, the flag address at F + 120),
     the atoms 75 / 87 / 88 and the alias SB + (F >> 3) = slot 88, as knock.
   - 0x80728-0x807c8: `bnez s2` decided by HPTR 5 on F (the real-stack path 0x8073c-0x80754 is never reached),
     `sd s8,0x10(s1)`, the frame header F[0..24) = 0x41B58AB3 / 0x1ffeb / 0x806b4, the 12 shadow bytes
     f1 x4, f8, f2 x3, f8, f3 x3 (0x80794-0x807c8).
   - 0x807cc `bnez a0` with a0 = n >> 26: split with SRr_sym_branch; the taken side (-> 0x80940) is refuted by
     n < 2 ^ 26 (atom 11); the fall-through runs to 0x807d0.
   - the join into ss_H (window 400) and the hand-off to the rest of the walk (RB).
   Section hypotheses: MTL TL LAWS ML ASM1 SMP FFL MTF and RB : rt_from B MT FP POST ss_H (INV_0 B MT 0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgMain0.v, with its module paths changed; 982 of its 1051 lines of code are new or changed and 218 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_scribble_encode_A.v, with its module paths, module names and addresses changed; 273 of its 328 lines of code are new or changed and 996 lines of the source are left out. *)
(* Image B: diginet_personality_from_name at 0x85090 is image A's code (lib/A/Prog/diginet_personality_from_name_A.v)
   instruction for instruction, each address 0x8b4 higher, with image B's strcmp wrapper (0x42424), personalities
   table (CB_PERS 0x9e240) and name rows (0x213c0 "CNTRL|24", 0x213e0 "MAINUNIT", rows 32 / 33 of CB_ROSTRS; each
   image-A row is 0x60 lower at image A). Image A's notes follow, with image B's addresses. *)
(* diginet_personality_from_name (diginet_codec.c:17-25) at image B: 0x85090, 43 instructions, frame 48; against
   lib/AU/Prog/CPgChkU.v's cdcU_from_name_specX at the image-A constants of lib/A/Prog/CPgWalk.v.
   The code: 0x850ac `beqz a0` (not taken: the atom fact 1 <= q of pfn_AF); the prologue saves ra, s0-s4; s1 = the
   shadow offset (the .got slot, then the cell), s3 = &personalities[0] (0x9e240), s2 = i = 0. A turn: s4 = s3 + 24 i,
   the instrumented check of the 8 bytes at s4 + 8 (its shadow byte, (s4 + 8) >> 3 + SB, folds to `SOff 32 off`: the
   shadow region of lib/A/Prog/CPgWalkImg.v, values from globs_marked, so the check's branch is decided), the load of
   personalities[i].announce_name from the image region (0x213c0 / 0x213e0, the rows "CNTRL|24" / "MAINUNIT" of
   CA_ROSTRS), then the strcmp wrapper at 0x850f8 (lib/A/Prog/CPgWalkStr.v cw_strcmp_cstr_at on the C string of tb and
   the name; the name's bytes from the image by cpw_rows_free, its crd_ok from cimg_rd's cimg_range). The re-seat at
   0x850fc keeps the five regions (the call writes only [sp - 48 - 2 ESTACK, sp - 48)) and puts a0 in the fresh atom
   44 (60 for the second turn). 0x8510c `bnez a1`, a1 = (a0 != 0) & (s2 ^ 1): split on the wrapper's value (taken:
   the second turn with s2 = 1; not taken: return); in the second turn a1 = .. & 0, so only the fall-through is
   reached. The result (a0 != 0) - 1 & s4 is s4 exactly when the strings are equal (pfn_U_sel), which is
   from_name_resA (pfn_res). The memory clause: the walk writes only [sp - 48 - 2 ESTACK, sp), inside T_from_name. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require Import StrcmpDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CodecRo CodecGlobs CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkRoU CPgWalkStrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfn_rs : smem := [cpg_img_region CB_PERS 48; cpg_shadow_region CB_PERS 48].
Definition pfn_AF : list (nat * afact) := [(10%nat, mkAF 1 (2 ^ 63) 0)].

(* the two announce names hold no 0 *)
Lemma pfn_c24_nz : ~ In 0 NAME_C24A.
Proof. cbn. intuition discriminate. Qed.
Lemma pfn_pca_nz : ~ In 0 NAME_PCA.
Proof. cbn. intuition discriminate. Qed.
(* diginet_personality_from_name's result on the C string s, its 0 and anything after *)
Lemma pfn_res : forall s rest, ~ In 0 s -> from_name_resA CB_PERS (s ++ 0 :: rest) =
if list_eq_dec Z.eq_dec s NAME_C24A then CB_PERS else if list_eq_dec Z.eq_dec s NAME_PCA then CB_PERS + 24 else 0.
Proof. intros s rest N. unfold from_name_resA. rewrite (cw_cstringZ_app s rest N). reflexivity. Qed.
(* `snez a0, a0 / xori a1, s2, 1 / and a1, a0, a1` with s2 = 0: a1 = (a0 != 0) *)
Lemma pfn_U_flag : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 ->
U E (SAlu ALU_AND (SAlu ALU_SLTU (SLit 0) (SOff n 0)) (SLit 1)) = if u =? 0 then 0 else 1.
Proof.
intros E n u Hn Hu. rewrite !U_SAlu, !U_SLit, (U_atom E n u Hn Hu). cbn [zalu_raw].
destruct (Z.eqb_spec u 0) as [->|Nz]; [vm_compute; reflexivity|].
replace (zcanon 0 <? u) with true by (symmetry; apply Z.ltb_lt; change (zcanon 0) with 0; lia).
vm_compute. reflexivity.
Qed.
(* `snez a0, a0 / addi a0, a0, -1 / and a0, a0, s4`: s4 when a0 was 0, else 0 *)
Lemma pfn_U_sel : forall E n u P, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 64 -> (P = 647744 \/ P = 647768) ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff n 0)) (SLit (-1))) (SLit P)) = if u =? 0 then P else 0.
Proof.
intros E n u P Hn Hu HP. rewrite !U_SAlu, !U_SLit, (U_atom E n u Hn Hu). cbn [zalu_raw].
destruct (Z.eqb_spec u 0) as [->|Nz]; [destruct HP as [-> | ->]; vm_compute; reflexivity|].
replace (zcanon 0 <? u) with true by (symmetry; apply Z.ltb_lt; change (zcanon 0) with 0; lia).
destruct HP as [-> | ->]; vm_compute; reflexivity.
Qed.
(* `and a1, a0, a1` with a1 = s2 ^ 1 = 0 *)
Lemma pfn_U_and0 : forall E x, U E (SAlu ALU_AND x (SLit 0)) = 0.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.land_0_r. reflexivity.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a region whose bytes the call kept and whose writable bytes are present after it *)
Lemma pfn_region_kept : forall E (H : word -> bool) (m m2 : word -> option byte) r,
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
  aview tfibsegs H m2 a = aview tfibsegs H m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
  apresent H m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) r.
Proof.
intros E H m m2 r Hv Hp. split; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hv. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
End a.
(* the re-seat at the return address of a call: the five regions kept (kept_tac), the clobbered registers in
   fresh atoms from K, the new environment named Ev with its equation HEv *)
Ltac pfn_reseat HS HJ2 HP2 K kept_tac Ev HEv :=
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
lazymatch type of HS with st_ok _ ?Enew _ _ => remember Enew as Ev eqn:HEv in HS end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis STRCMP : astrcmp_realizes tfibsegs B 0x42424.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Theorem diginet_personality_from_name_B_holds :
cdcU_from_name_specX tfibsegs B MT CB_RLO CB_RHI CB_PERS CB_ROSTRS 0x85090.
Proof.
unfold cdcU_from_name_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q tb HE H10 HCS HCI.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_from_name HE
  ltac:(unfold TB_from_name, ESTACK; lia)) as (Hceil & H47 & H46 & Hal16 & Hpres).
destruct HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hwlo as HwloT.
unfold TB_from_name in Hwlo, H46, Hceil, Hpres. rewrite Hes in Hwlo, H46, Hceil, Hpres.
destruct HCS as (Hq0 & HTB & HIN & HCRD).
destruct HCI as (HRO & HROWS).
pose proof (proj1 HJ) as HAR.
pose proof HCRD as (_ & Hqn & _ & _ & _ & _ & Hqw). unfold coff_win, TB_from_name in Hqw. rewrite Hes in Hqw.
assert (Hq63 : q < 2 ^ 63).
{ destruct tb as [|b tb]; [destruct HIN|]. cbn [length] in Hqn. lia. }
pose proof (Forall_inv HROWS) as (HPro & HPcr). cbn [fst snd] in HPro, HPcr.
assert (HS : st_ok tfibsegs (Ereg regs (cw_extra []))
  (mkSS 0x85090 sr_atoms (cw_regs 48 ++ pfn_rs) None (mkFacts (cw_atoms ++ pfn_AF) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x85090) memc (seg_rom tfibsegs)))).
{ apply (cw_entry B TL LAWS 0x85090 48 [] pfn_rs pfn_AF lyc Sc W regs memc mdc HAR ltac:(lia) ltac:(lia) Hal16
    ltac:(intros a Ha; apply Hpres; lia) ltac:(vm_compute; reflexivity)).
  - unfold pfn_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (cpg_img_region_ok B CB_RLO CB_RHI _ W memc CB_PERS 48 HRO).
      * intros a Ha. replace a with (CB_PERS + (a - CB_PERS)) by lia. apply HPro. lia.
      * intros a Ha. apply (proj1 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, CB_PERS in *; lia))).
      * intros a Ha. apply (proj2 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, CB_PERS in *; lia))).
      * vm_compute. reflexivity.
      * unfold CB_PERS; lia.
      * lia.
      * unfold CB_PERS; lia.
    + apply (cpg_shadow_region_ok B _ W memc lyc Sc mdc CODEC_GLOBS CB_PERS 48 GM cg_PERS HAR (cw_ew_SB regs []));
      unfold CB_PERS; lia.
  - apply pairwise_disjoint_of_extents.
    let rs' := eval vm_compute in (cw_regs 48 ++ pfn_rs) in change (cw_regs 48 ++ pfn_rs) with rs'.
    unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), cw_ew_SB. change (bv_unsigned (getr regs 2)) with (spZ regs).
    rewrite unsigned_lit_small by (unfold SB; lia). unfold SB.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - cbn [pfn_AF atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; first [lia | exact I]. }
remember (Ereg regs (cw_extra [])) as E eqn:HEq.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (ERA : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (cw_ew_reg regs [] 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (cw_ew_reg regs [] 4 4%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
clear HEq.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 0x85090) with (Z_to_bv 64 0x85090).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
destruct (cw_cstr_split tb HIN) as (s & rest & Htb & NS).
assert (HLs : Z.of_nat (length s) + 1 <= Z.of_nat (length tb)) by (rewrite Htb, length_app; cbn [length]; lia).
assert (CS0 : cw_cstr_at W memc q s) by (rewrite Htb in HTB; exact (cw_cstr_of_garr8 W memc q s rest HTB NS)).
assert (HinN1 : In (0x213c0, 9) CB_ROSTRS) by (apply globs_In_b; vm_compute; reflexivity).
pose proof (proj1 (Forall_forall _ _) HROWS (0x213c0, 9) (in_cons _ _ _ HinN1)) as (HroN1 & HcrN1).
cbn [fst snd] in HroN1, HcrN1.
assert (CN1 : cw_cstr_at W memc 0x213c0 NAME_C24A)
  by (apply (cw_cstr_row B CB_RLO CB_RHI W memc CB_ROSTRS 0x213c0 9 NAME_C24A HRO RF HinN1 HroN1);
      [cbn; lia | vm_compute; reflexivity]).
assert (HinN2 : In (0x213e0, 9) CB_ROSTRS) by (apply globs_In_b; vm_compute; reflexivity).
pose proof (proj1 (Forall_forall _ _) HROWS (0x213e0, 9) (in_cons _ _ _ HinN2)) as (HroN2 & HcrN2).
cbn [fst snd] in HroN2, HcrN2.
assert (CN2 : cw_cstr_at W memc 0x213e0 NAME_PCA)
  by (apply (cw_cstr_row B CB_RLO CB_RHI W memc CB_ROSTRS 0x213e0 9 NAME_PCA HRO RF HinN2 HroN2);
      [cbn; lia | vm_compute; reflexivity]).
set (o := spZ regs - 48 - sp0).
assert (Ho : sp0 + o = spZ regs - 48) by (unfold o; lia).
assert (Hom : o mod 16 = 0).
{ unfold o. rewrite Zminus_mod, (Zminus_mod (spZ regs) 48), Hal16, Hsp0al. reflexivity. }
cw_run ltac:(cw_awr_stk).
cw_keep ltac:(cw_kwr_stk).
cbv beta in KE.
(* the call of the strcmp wrapper at 0x850f8: strcmp(q, "CNTRL|24") *)
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
  assert (Rsp : spZ (ms_regs m) = sp0 + o) by (rewrite Ho; unfold spZ at 1; rewrite R2, B2; apply unsigned_lit_small; lia) end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT _ _ =>
  assert (CS1 : cw_cstr_at W mT q s) by (apply (cw_cstr_kept W memc _ q s (spZ regs - 48) (spZ regs) CS0 KE); lia);
  assert (CN1T : cw_cstr_at W mT 0x213c0 NAME_C24A)
    by (apply (cw_cstr_kept W memc _ 0x213c0 NAME_C24A (spZ regs - 48) (spZ regs) CN1 KE); cbn; lia) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (cw_strcmp_cstr_at B LAWS 0x42424 STRCMP W _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k q 0x213c0 s
    NAME_C24A o _ HJ).
  - rewrite R10, E10. reflexivity.
  - rewrite R11. reflexivity.
  - lia.
  - lia.
  - exact Rsp.
  - exact Hom.
  - unfold o; lia.
  - unfold o; lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - right. cbn. lia.
  - exact CS1.
  - exact CN1T.
  - rewrite Ho. apply (cw_crd_kept W memc _ (spZ regs - 48) (2 * ESTACK) q _ (spZ regs - 48) (spZ regs)); [| exact KE | lia | lia].
    apply (cw_crd_win W memc (spZ regs) TB_from_name); [| lia | unfold TB_from_name; lia].
    apply (cw_crd_sub W memc (spZ regs) TB_from_name q (Z.of_nat (length tb))); [exact HCRD | lia | lia | lia].
  - rewrite Ho. change (Z.of_nat (length NAME_C24A) + 1) with 9.
    apply (cw_crd_img B lyc Sc W _ _ (spZ regs) TB_from_name 0x213c0 9 (spZ regs - 48) (2 * ESTACK) HcrN1 (proj1 HJ));
    [exact (cw_cstr_rd W _ _ _ CN1T) | lia | unfold TB_from_name; lia]. }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame2 & Hv2 & Hfr2 & Hpres2).
rewrite Ho in Hfr2. clear R1 R2 R3 R4 R10 R11 Rsp.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp2 & _).
pfn_reseat HS HJ2 HP2 40%nat ltac:(idtac;
  apply pfn_region_kept; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  try rewrite (AG 2%nat) by lia; try rewrite (AG 32%nat) by lia; rewrite ?B2, ?E32, ?unsigned_lit_small by (unfold SB; lia);
  intros a Ha; [apply Hfr2; unfold SB in *; lia | apply HJp2; lia]) Ec1 HEc1.
assert (AG1 : forall n, (n < 33)%nat -> ew Ec1 n = ew E n)
  by (intros nn Hnn; rewrite HEc1, ew_havoc_old by lia; apply AG; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs (cw_extra [])) Ec1)
  by (rewrite HEc1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (EV1 : ew Ec1 44 = w64 (cw_strcmpZ s NAME_C24A))
  by (rewrite HEc1, (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact Hv2).
clear HEc1. clear HJ. rename HJ2 into HJ.
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - 2 * ESTACK <= a < spZ regs) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a)
  by (intros a Ha Hn; rewrite (Hfr2 a Ha) by lia; apply KE; [exact Ha | lia]).
clear KE Hfr2. rename KE2 into KE.
clear SHOK. assert (SHOK : sh_ok tfibsegs CW_Bx [] Ec1 (mrestrict (w_H W) mem2)) by constructor.
assert (B21 : bv_unsigned (ew Ec1 2) = spZ regs) by (rewrite AG1 by lia; exact B2).
cw_run ltac:(cw_awr_stk).
cw_keep ltac:(cw_kwr_stk).
cbv beta in KE.
set (u1 := bv_unsigned (w64 (cw_strcmpZ s NAME_C24A))).
assert (EU1 : ew Ec1 44 = Z_to_bv 64 u1) by (rewrite EV1; unfold u1; symmetry; apply Z_to_bv_bv_unsigned).
assert (Ru1 : 0 <= u1 < 2 ^ 64)
  by (unfold u1; pose proof (bv_unsigned_in_range 64 (w64 (cw_strcmpZ s NAME_C24A))) as R;
      change (bv_modulus 64) with (2 ^ 64) in R; exact R).
pose proof (cw_strcmpZ_unsigned s NAME_C24A NS pfn_c24_nz) as CU1. fold u1 in CU1.
assert (EF1 : ew Ec1 1 = getr regs 1) by (rewrite AG1 by lia; exact ERA).
(* 0x8510c bnez a1: a1 = (a0 != 0) & (s2 ^ 1), s2 = 0 *)
cw_branch Hb.
all: rewrite branch_ne_U, (pfn_U_flag _ 44 u1 EU1 Ru1), U_lit in Hb by lia; revert Hb.
all: destruct (Z.eqb_spec u1 0) as [U0|U0]; intros Hb; cbn in Hb; try discriminate Hb.
2:{ (* not taken: strcmp(q, "CNTRL|24") = 0, a0 = personalities + 0 *)
  assert (Es : s = NAME_C24A) by (apply CU1; exact U0).
  cw_run ltac:(cw_awr_stk).
  cw_keep ltac:(cw_kwr_stk).
  cbv beta in KE.
  cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(idtac; intros ? [])
      ltac:(idtac; intros a Ha; cbv beta in Ha; left; unfold TB_from_name; lia))
  ltac:(cbv beta; rewrite R10, denot_lit_U, (pfn_U_sel _ 44 u1 647744 EU1 Ru1 (or_introl eq_refl)),
    (proj2 (Z.eqb_eq u1 0) U0), Htb, (pfn_res s rest NS);
    destruct (list_eq_dec Z.eq_dec s NAME_C24A) as [_|C]; [reflexivity | exfalso; exact (C Es)]). }
(* taken: strcmp(q, "CNTRL|24") <> 0, the second turn *)
assert (N1 : s <> NAME_C24A) by (intros C; apply U0; apply CU1; exact C).
cw_run ltac:(cw_awr_stk).
cw_keep ltac:(cw_kwr_stk).
cbv beta in KE.
(* the call of the strcmp wrapper at 0x850f8 again: strcmp(q, "MAINUNIT") *)
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
  assert (Rsp : spZ (ms_regs m) = sp0 + o) by (rewrite Ho; unfold spZ at 1; rewrite R2, AG1, B2 by lia; apply unsigned_lit_small; lia) end.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT _ _ =>
  assert (CS2 : cw_cstr_at W mT q s)
    by (apply (cw_cstr_kept W memc _ q s (spZ regs - 48 - 2 * ESTACK) (spZ regs) CS0 KE); lia);
  assert (CN2T : cw_cstr_at W mT 0x213e0 NAME_PCA)
    by (apply (cw_cstr_kept W memc _ 0x213e0 NAME_PCA (spZ regs - 48 - 2 * ESTACK) (spZ regs) CN2 KE); cbn; lia) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (cw_strcmp_cstr_at B LAWS 0x42424 STRCMP W _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k q 0x213e0 s
    NAME_PCA o _ HJ).
  - rewrite R10, AG1, E10 by lia. reflexivity.
  - rewrite R11. reflexivity.
  - lia.
  - lia.
  - exact Rsp.
  - exact Hom.
  - unfold o; lia.
  - unfold o; lia.
  - rewrite R3, AG1, E3 by lia. exact Hgp.
  - rewrite R4, AG1, E4 by lia. exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - right. cbn. lia.
  - exact CS2.
  - exact CN2T.
  - rewrite Ho.
    apply (cw_crd_kept W memc _ (spZ regs - 48) (2 * ESTACK) q _ (spZ regs - 48 - 2 * ESTACK) (spZ regs)); [| exact KE | lia | lia].
    apply (cw_crd_win W memc (spZ regs) TB_from_name); [| lia | unfold TB_from_name; lia].
    apply (cw_crd_sub W memc (spZ regs) TB_from_name q (Z.of_nat (length tb))); [exact HCRD | lia | lia | lia].
  - rewrite Ho. change (Z.of_nat (length NAME_PCA) + 1) with 9.
    apply (cw_crd_img B lyc Sc W _ _ (spZ regs) TB_from_name 0x213e0 9 (spZ regs - 48) (2 * ESTACK) HcrN2 (proj1 HJ));
    [exact (cw_cstr_rd W _ _ _ CN2T) | lia | unfold TB_from_name; lia]. }
cbv beta. intros W3 cf _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hsame3 & Hv3 & Hfr3 & Hpres3).
rewrite Ho in Hfr3. clear R1 R2 R3 R4 R10 R11 Rsp.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp3 & _).
pfn_reseat HS HJ3 HP3 60%nat ltac:(idtac;
  apply pfn_region_kept; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  try rewrite (AG1 2%nat) by lia; try rewrite (AG1 32%nat) by lia; rewrite ?B2, ?E32, ?unsigned_lit_small by (unfold SB; lia);
  intros a Ha; [apply Hfr3; unfold SB in *; lia | apply HJp3; lia]) Ec2 HEc2.
assert (AG2 : forall n, (n < 33)%nat -> ew Ec2 n = ew E n)
  by (intros nn Hnn; rewrite HEc2, ew_havoc_old by lia; apply AG1; exact Hnn).
assert (HAE2 : env_agree 32 (Ereg regs (cw_extra [])) Ec2)
  by (rewrite HEc2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (EV2 : ew Ec2 64 = w64 (cw_strcmpZ s NAME_PCA))
  by (rewrite HEc2, (ew_havoc_new _ 60 _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact Hv3).
clear HEc2. clear HJ. rename HJ3 into HJ.
assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - 2 * ESTACK <= a < spZ regs) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) memc a)
  by (intros a Ha Hn; rewrite (Hfr3 a Ha) by lia; apply KE; [exact Ha | lia]).
clear KE Hfr3. rename KE3 into KE.
clear SHOK. assert (SHOK : sh_ok tfibsegs CW_Bx [] Ec2 (mrestrict (w_H W) mem3)) by constructor.
assert (B22 : bv_unsigned (ew Ec2 2) = spZ regs) by (rewrite AG2 by lia; exact B2).
assert (EF2 : ew Ec2 1 = getr regs 1) by (rewrite AG2 by lia; exact ERA).
cw_run ltac:(cw_awr_stk).
cw_keep ltac:(cw_kwr_stk).
cbv beta in KE.
set (u2 := bv_unsigned (w64 (cw_strcmpZ s NAME_PCA))).
assert (EU2 : ew Ec2 64 = Z_to_bv 64 u2) by (rewrite EV2; unfold u2; symmetry; apply Z_to_bv_bv_unsigned).
assert (Ru2 : 0 <= u2 < 2 ^ 64)
  by (unfold u2; pose proof (bv_unsigned_in_range 64 (w64 (cw_strcmpZ s NAME_PCA))) as R;
      change (bv_modulus 64) with (2 ^ 64) in R; exact R).
pose proof (cw_strcmpZ_unsigned s NAME_PCA NS pfn_pca_nz) as CU2. fold u2 in CU2.
(* 0x8510c bnez a1 with s2 = 1: a1 = (a0 != 0) & 0, not taken *)
cw_branch Hb2.
{ exfalso. rewrite branch_ne_U, pfn_U_and0, U_lit in Hb2 by lia. discriminate Hb2. }
cw_run ltac:(cw_awr_stk).
cw_keep ltac:(cw_kwr_stk).
cbv beta in KE.
cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(idtac; intros ? [])
    ltac:(idtac; intros a Ha; cbv beta in Ha; left; unfold TB_from_name; lia))
ltac:(cbv beta; rewrite R10, denot_lit_U, (pfn_U_sel _ 64 u2 647768 EU2 Ru2 (or_intror eq_refl)), Htb, (pfn_res s rest NS);
  destruct (list_eq_dec Z.eq_dec s NAME_C24A) as [C|_]; [exfalso; exact (N1 C)|];
  destruct (list_eq_dec Z.eq_dec s NAME_PCA) as [P|P]; destruct (Z.eqb_spec u2 0) as [U2|U2];
  first [reflexivity | exfalso; apply U2; apply CU2; exact P | exfalso; apply P; apply CU2; exact U2]).
Qed.
End d.
End b.
