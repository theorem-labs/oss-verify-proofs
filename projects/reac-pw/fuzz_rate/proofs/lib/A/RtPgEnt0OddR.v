(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths and module names changed; 220 of its 256 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its engine runs o_run1a .. o_run4 and their plumbing) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the code is rate's 24 words 0x81b6c .. 0x81bcc; the shadow token's base is s2 (atom 18) in place of s7; the entry goes to s8 (x24) in place of s9; the copy's destination is s6 (x22) in place of s4; the last run is rate's lone `j` to G 0x8150c (no `mv s9,s8`); RPgSteps / RPgMem / RPgCfgChanges are lib/A/RtPgSteps.v, RtPgMem.v and lib/A/RtPgW7bBase.v's w7_kept_run / w7_same_io_wvb; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the engine runs of the ODD
   block of ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`)
   from 0x81b6c to G = 0x8150c, over the journal (no cut state). Proves no function (kind: segment lemma).

   THE CODE and how the walk cuts it:
     1a 0x81b6c .. 0x81b94  a1 := the constant 0x124924924924924a (`ld` of .rodata 0x10318), a0 := c mod 14 (the
                            `mulhu` chain), a2 := 0x9bb84 (`auipc`), a0 := 0x9bb40 + 8 (c mod 14), the table entry
                            (checked on every c in [200, 256) by o_all56)
     1b 0x81b98 .. 0x81ba8  the shadow check of that table entry (`srli`, `add s2`, `lbu`, `beqz`, else `j` to the
                            report 0x83398): one obligation of the token engine, range_addressable of the entry's 8 bytes
     2  0x81bac .. 0x81bb4  s8 := the entry (odd_ch[c mod 14], a cell of .data.rel.ro), a0 := s8, `jal` strlen
        0x42194             the strlen wrapper (Rt/StrlenDef.v astrlen_realizes, RtPgW7bCall.w7_strlen_at)
     3  0x81bb8 .. 0x81bc4  a2 := len + 1, a0 := s6 (= &ch = F + 0xa0), a1 := s8, `jal` __asan_memcpy
        0x51860             __asan_memcpy (YG0d.v aintrin_realizes OCpy, RtPgW7bKit.w7_memcpy_at)
     4  0x81bc8             `j` 0x8150c
   Run 1 is cut at 0x81b98 because the engine keeps no range for a `mulhu` result and folds `(x << 3 + K) >> 3`
   into an offset of x when it has one, and its shadow token matches only `(x >> 3) + s2`: run 1b starts from a
   fresh atom for the entry's address with the table's range and 8-alignment. Each run is an engine run
   (lib/Reusable/YCbq.v aj_run_to_tok) from a fresh symbolic state to the run's end pc, with RtPgW7bBase.w7_post as
   its post; lib/A/RtPgEnt0OddW.v chains them. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW7bBase RtPgEnt0OddB.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ---- the code: the 24 words 0x81b6c .. 0x81bcc ---- *)
Definition O_PC : Z := 0x81b6c.
Definition o_tbl : ctable := build_table rsegs O_PC 24 TEmpty.
Lemma o_tbl_ok : table_ok rsegs o_tbl.
Proof. apply build_table_ok0. unfold O_PC. lia. Qed.
(* the constant 0x124924924924924a at .rodata 0x10318 is 8 image bytes *)
Lemma o_k14_rom : rom_run_b 0x10318 8 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- a value of the engine that is a function of c, checked on every c in [200, 256) ---- *)
Lemma o_all56 : forall f : Z -> Z,
forallb (fun i => f (200 + Z.of_nat i) =? O_TBL + 8 * ((200 + Z.of_nat i) mod 14)) (seq 0 56) = true ->
forall c, 200 <= c < 256 -> f c = O_TBL + 8 * (c mod 14).
Proof.
intros f H c Hc. rewrite forallb_forall in H.
specialize (H (Z.to_nat (c - 200)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
replace (200 + (c - 200)) with c in H by lia. apply Z.eqb_eq. exact H.
Qed.
Ltac o_refl56 c Hc :=
lazymatch goal with |- ?L = _ =>
  let f := eval pattern c in L in
  lazymatch f with ?g c => apply (o_all56 g); [vm_compute; reflexivity | exact Hc] end end.

(* ---- engine plumbing ---- *)
(* the value of register r at a run's last state *)
Ltac o_reg HS r :=
rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end.
(* a region list without a write window writes nothing *)
Ltac o_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.

(* an atom below 32 of a run's last environment is the register it started as *)
Lemma o_agree_atom : forall regs extra Ev n (r : bv 5), env_agree 32 (Ereg regs extra) Ev -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned r -> sv_denot Ev (SOff n 0) = getr regs r.
Proof.
intros regs extra Ev n r [HA _] Hn Hr. apply bv_eq.
rewrite denot_SOff, (HA n Hn), (ew_Ereg_nat regs extra n r Hr), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ======================== run 1a: 0x81b6c -> 0x81b98 ======================== *)
Definition ss_O1a : sstate :=
mkSS O_PC sr_atoms [YP09.mkRegion None 0x10318 (0x10318 + 8) 0 0 [YP09.mkChunk 0x10318 (CImg 8)]] None
  (mkFacts [] [] []).

Lemma o_run1a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 c -> 200 <= c < 256 -> rom_view rsegs W memc ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 O_PC) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81b98 regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (O_TBL + 8 * (c mod 14)))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ H10 Hc HR.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HS : st_ok rsegs (Ereg regs []) ss_O1a (restrict (w_H W) (mkst regs (Z_to_bv 64 O_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact o_k14_rom].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK W7Bspan 0x81b98.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + o_reg HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (E10' : ew Ev 10 = Z_to_bv 64 c)
        by (assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE;
            try rewrite (proj1 HA' 10%nat ltac:(lia)); exact E10) end.
    rewrite !U_SAlu, !U_SMd, !U_SLit, (U_atom _ 10 c E10') by lia.
    o_refl56 c Hc.
Qed.

(* ======================== run 1b: 0x81b98 -> 0x81bac ========================
   a0 is a fresh atom with the table's range and 8-alignment, so the engine's shadow token matches `(a0 >> 3) + s2`
   at the `lbu` and leaves the entry's range_addressable as the one obligation. *)
Definition ss_O1b : sstate :=
mkSS 0x81b98 sr_atoms [] None (mkFacts [(18%nat, mkAF W7SB W7SB 0); (10%nat, mkAF O_TBL (O_TBL + 104) 3)] [] []).

Lemma o_run1b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 10 = w64 (O_TBL + 8 * m) -> 0 <= m < 14 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (O_TBL + 8 * m) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81b98) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81bac regs memc mdc [11]%bv (fun _ => False)
(fun _ _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ H18 H10 Hm HRA.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (E18 : ew (Ereg regs []) 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 (O_TBL + 8 * m))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Hal : (O_TBL + 8 * m) mod 8 = 0).
{ replace (O_TBL + 8 * m) with ((79720 + m) * 8) by (unfold O_TBL; lia). apply Z.mod_mul. lia. }
assert (HS : st_ok rsegs (Ereg regs []) ss_O1b (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81b98) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_O1b f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E18, E10, H18. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, O_TBL; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. rewrite Hal.
    unfold SHADOW_OFF, W7SB, O_TBL. repeat split; lia. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK W7Bspan 0x81bac.
- (* the shadow obligation of the table entry *)
  cbn [ms_mem mkst]. unfold W7Bx.
  rewrite (U_atom _ 18 SHADOW_OFF) by first [rewrite E18, H18; reflexivity | unfold SHADOW_OFF; lia].
  rewrite (U_atom _ 10 (O_TBL + 8 * m) E10) by (unfold O_TBL; lia).
  exact HRA.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + exact I.
Qed.

(* ======================== run 2: 0x81bac -> 0x42194 (strlen) ======================== *)
Definition ss_O2 : sstate :=
mkSS 0x81bac sr_atoms [YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [] [] []).

Lemma o_run2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) a o,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 a -> 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) a 8 o ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81bac) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_STRLEN regs memc mdc [1; 10; 24]%bv (fun _ => False)
(fun regs2 _ => getr regs2 24 = w64 o /\ getr regs2 10 = w64 o /\ getr regs2 1 = w64 0x81bb8)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs a o HJ H10 Ha0 Ha8 Ho Hval.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (B10 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 o]) 10) = a)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs [Z_to_bv 64 o]) 32 = Z_to_bv 64 o) by exact (ew_Ereg_extra regs [Z_to_bv 64 o] 0).
assert (D32 : sv_denot (Ereg regs [Z_to_bv 64 o]) (SOff 32 0) = Z_to_bv 64 o).
{ apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 o]) ss_O2 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81bac) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtm_ro_region rsegs _ (w_H W) memc 10%nat a 0 8); [exact B10 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ a 0 8 (SOff 32 0) o);
      [exact D32 | change (8 * Z.of_N 8) with 64; lia | cbn; lia | rewrite Z.add_0_r; exact Hval].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs [Z_to_bv 64 o]) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 o]) (Ereg regs [Z_to_bv 64 o])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK W7Bspan 0x42194.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [Z_to_bv 64 o] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + split; [|split].
    * o_reg HS (24%bv : bv 5). exact D32.
    * o_reg HS (10%bv : bv 5). exact D32.
    * o_reg HS (1%bv : bv 5). reflexivity.
Qed.

(* ======================== run 3: 0x81bb8 -> 0x51860 (__asan_memcpy) ======================== *)
Definition ss_Opc (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma o_run3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 n -> 0 <= n -> n + 1 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81bb8) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc [1; 10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 12 = w64 (n + 1) /\ getr regs2 10 = getr regs 22 /\ getr regs2 11 = getr regs 24 /\
  getr regs2 1 = w64 0x81bc8)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HJ H10 Hn0 Hn1.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x81bb8) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81bb8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK W7Bspan 0x51860.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE end.
    split; [|split; [|split]].
    * o_reg HS (12%bv : bv 5). cbn [sv_denot].
      try rewrite (proj1 HA' 10%nat ltac:(lia)). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * o_reg HS (10%bv : bv 5). exact (o_agree_atom regs [] _ 22 22%bv HA' ltac:(lia) eq_refl).
    * o_reg HS (11%bv : bv 5). exact (o_agree_atom regs [] _ 24 24%bv HA' ltac:(lia) eq_refl).
    * o_reg HS (1%bv : bv 5). reflexivity.
Qed.

(* ======================== run 4: 0x81bc8 -> G 0x8150c ======================== *)
Lemma o_run4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81bc8) memc (seg_rom rsegs)) mdc)
(w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x8150c regs memc mdc [] (fun _ => False)
(fun _ _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7_wx as Hwx. pose proof w7_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x81bc8) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81bc8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK W7Bspan 0x8150c.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7_same_io_wvb | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + exact I.
Qed.
End d.
End b.

Print Assumptions o_run1a.
Print Assumptions o_run1b.
Print Assumptions o_run2.
Print Assumptions o_run3.
Print Assumptions o_run4.
