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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v, with its module paths and module names changed; 270 of its 306 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its memory facts and o_walk; the engine runs are in lib/A/RtPgEnt0OddR.v) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the shadow offset is in s2 (x18), &ch in s6 (x22), the entry in s8 (x24), so s8 is the one callee-saved register the block changes and there is no `s9 := s8`; G is 0x8150c; the strings lie below 0x21400; the frame's shadow has 56 bytes (RtPgMem.rtm_sh, seven flags); RPgMem / RPgBase are lib/A/RtPgMem.v / RtPgBase.v (rtm_*, rt_cstr, rt_fsh); the kit is lib/A/RtPgW7bKit.v / RtPgW7bCall.v; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddW.v, with its module paths, module names, addresses and numbers changed; 349 of its 575 lines of code are new or changed and 80 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 97ea9c9eafa; image B of
   fuzz_headamp's ODD block 0x82318 .. 0x82388 re-walked instruction by instruction (its own registers: a3 = c,
   s2 = &ch, t1 = what is left of the input, s4 = the table entry, s5 = t1 across the two calls, s11 = K), image
   B's UBSan pointer-overflow test `bgeu a2,a0` 0x82344 added as a run of its own, the shadow base E0Bx = SOff 27 0
   (image A: s7 = atom 23), the strlen wrapper at 0x41c18 and __asan_memcpy at 0x51d8c, the frame of class 4 (1024
   bytes, 116 shadow bytes, ch at F+0xa0), the kit lemmas taken from lib/AU/HPgE0Base.v, prefix e0_, and from
   lib/A/HPgMem.v, prefix hm_, and the allocator laws taken from the kernel theorem AR_laws_ok instead of a
   Section hypothesis. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the walk of the ODD block
   of ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`) from
   0x82318 to G = 0x81afc, over the journal (no cut state). Proves no function (kind: segment lemma).

   THE CODE and how the walk cuts it:
     A  0x82318 .. 0x8233c  a1 := the constant 0x124924924924924a (`ld` of .rodata 0x10318), a0 := 8 (c mod 14)
                            (the `mulhu` chain), a1 := 0x9c560 (`auipc` + `addi`); the value of a0 is checked on
                            every c in [200, 256) by o_all56
     B  0x82340 .. 0x82360  `not a2,a1`, the UBSan pointer-overflow test `bgeu a2,a0` (its trap arm `j 0x83a14`
                            0x82348 is not taken: a0 <= 104 and a2 = ~0x9c560), a0 := 0x9c560 + 8 (c mod 14), and
                            the shadow check of that table entry (`srli`, `add s11`, `lbu`, `beqz`, else `j` to the
                            report): one obligation of the token engine, range_addressable of the entry's 8 bytes
     C  0x82364 .. 0x82370  s5 := t1 (what is left of the input, kept across the two calls), s4 := the entry
                            (odd_ch[c mod 14], a cell of .data.rel.ro), a0 := s4, `jal` 0x41c18, the strlen wrapper
                            (lib/A/Rt/StrlenDef.v astrlen_realizes, HPgE0Base.e0_strlen_at)
     D  0x82374 .. 0x82380  a2 := len + 1, a0 := s2 (= &ch = F + 0xa0), a1 := s4, `jal` 0x51d8c, __asan_memcpy
                            (YG0d.v aintrin_realizes OCpy, HPgE0Base.e0_memcpy_at)
     E  0x82384 .. 0x82388  t1 := s5, `j` 0x81afc
   Run A stops before `not a2,a1` because the engine keeps no range for a `mulhu` result and so cannot decide the
   pointer-overflow test; run B starts from a fresh atom for 8 (c mod 14) with the range [0, 104] and 8-alignment,
   with a1 pinned to the table's address, which decides the test and makes the engine's shadow token match
   `(a0 >> 3) + s11`. Each run is an engine run (lib/Reusable/YCbq.v aj_run_to_tok) from a fresh symbolic state to
   the run's end pc, with HPgCaseB.cb_post as its post. o_walk chains them: the journal kept, the callee-saved
   registers but s4 and s5 kept, t1 kept, every byte outside the callees' stack [R - 2 ESTACK, R) and ch's len + 1
   bytes kept, and ch holding the string and its NUL. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgMem HPgE0Base HPgE0OddB HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code: the 29 words 0x82318 .. 0x82388 ---- *)
Definition O_PC : Z := 0x82318.
Definition o_tbl : ctable := build_table rsegs O_PC 29 TEmpty.
Lemma o_tbl_ok : table_ok rsegs o_tbl.
Proof. apply build_table_ok0. unfold O_PC. lia. Qed.

(* ---- a value of the engine that is a function of c, checked on every c in [200, 256) ---- *)
Lemma o_all56 : forall f g : Z -> Z,
forallb (fun i => f (200 + Z.of_nat i) =? g (200 + Z.of_nat i)) (seq 0 56) = true ->
forall c, 200 <= c < 256 -> f c = g c.
Proof.
intros f g H c Hc. rewrite forallb_forall in H.
specialize (H (Z.to_nat (c - 200)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
replace (200 + (c - 200)) with c in H by lia. apply Z.eqb_eq. exact H.
Qed.
Ltac o_refl56 c Hc :=
lazymatch goal with |- ?L = ?R =>
  let f := eval pattern c in L in
  let g := eval pattern c in R in
  lazymatch f with ?ff c =>
  lazymatch g with ?gg c => apply (o_all56 ff gg); [vm_compute; reflexivity | exact Hc] end end end.

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
(* a register outside a concrete clobber list *)
Ltac o_notin :=
let H := fresh "H" in intros H; cbn [In] in H;
repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]); exact H.
Ltac o_keep Hk := rewrite Hk by first [cbv; discriminate | o_notin].

(* an atom below 32 of a run's last environment is the register it started as *)
Lemma o_agree_atom : forall regs extra Ev n (r : bv 5), env_agree 32 (Ereg regs extra) Ev -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned r -> sv_denot Ev (SOff n 0) = getr regs r.
Proof.
intros regs extra Ev n r [HA _] Hn Hr. apply bv_eq.
rewrite denot_SOff, (HA n Hn), (ew_Ereg_nat regs extra n r Hr), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

(* a callee-saved register other than s4 and s5 is outside every clobber list of the walk *)
Lemma o_cs_kept : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
(forall q : bv 5, In q clob -> In (bv_unsigned q) [1; 6; 10; 11; 12; 20; 21]) ->
forall r, acallee_saved r -> r <> 20 -> r <> 21 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' clob Hk Hc r Hr H20 H21.
assert (Hu : bv_unsigned (Z_to_bv 5 r) = r).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold acallee_saved in Hr.
  apply Z.mod_small. lia. }
apply Hk.
- rewrite Hu. unfold acallee_saved in Hr. lia.
- intros Hin. pose proof (Hc _ Hin) as Hq. rewrite Hu in Hq. cbn [In] in Hq. unfold acallee_saved in Hr. lia.
Qed.
Ltac o_clob := let q := fresh "q" in let Hq := fresh "Hq" in
intros q Hq; cbn [In] in Hq;
repeat (destruct Hq as [<-|Hq]; [cbn [In]; repeat (first [left; reflexivity | right]) |]); destruct Hq.

(* t1 (x6) is kept by every clobber list but run E's *)
Lemma o_t1_kept : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
(forall q : bv 5, In q clob -> In (bv_unsigned q) [1; 10; 11; 12; 20; 21]) ->
getr regs' 6 = getr regs 6.
Proof.
intros regs regs' clob Hk Hc. apply Hk; [vm_compute; discriminate|].
intros Hin. pose proof (Hc _ Hin) as Hq. vm_compute in Hq. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ======================== run A: 0x82318 -> 0x82340 ======================== *)
Definition ss_OA : sstate :=
mkSS O_PC sr_atoms [YP09.mkRegion None 0x10318 (0x10318 + 8) 0 0 [YP09.mkChunk 0x10318 (CImg 8)]] None
  (mkFacts [] [] []).

Lemma o_runA : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 13 = w64 c -> 200 <= c < 256 -> rom_view rsegs W memc ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 O_PC) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x82340 regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (8 * (c mod 14)) /\ getr regs2 11 = w64 O_TBL)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ H13 Hc HR.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (HS : st_ok rsegs (Ereg regs []) ss_OA (restrict (w_H W) (mkst regs (Z_to_bv 64 O_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact o_k14_rom].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK E0Bspan 0x82340.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (E13' : ew Ev 13 = Z_to_bv 64 c)
        by (assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE;
            try rewrite (proj1 HA' 13%nat ltac:(lia)); exact E13) end.
    split.
    * o_reg HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      rewrite !U_SAlu, !U_SMd, !U_SLit, (U_atom _ 13 c E13') by lia.
      o_refl56 c Hc.
    * o_reg HS (11%bv : bv 5). reflexivity.
Qed.

(* ======================== run B: 0x82340 -> 0x82364 ========================
   a0 is a fresh atom for 8 (c mod 14) with the range [0, 104] and 8-alignment and a1 is pinned to the table's
   address, so the UBSan test `bgeu a2,a0` is decided, the engine's shadow token matches `(a0 >> 3) + s11` at the
   `lbu`, and the entry's range_addressable is the one obligation. *)
Definition ss_OB0 : sstate :=
mkSS 0x82340 sr_atoms [] None (mkFacts [(27%nat, mkAF E0SB E0SB 0); (10%nat, mkAF 0 104 3)] [] []).
Definition ss_OB : sstate :=
mkSS 0x82340 (sr_set sr_atoms 11%bv (SLit O_TBL)) [] None
  (mkFacts [(27%nat, mkAF E0SB E0SB 0); (10%nat, mkAF 0 104 3)] [] []).

Lemma o_runB : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 10 = w64 (8 * m) -> getr regs 11 = w64 O_TBL -> 0 <= m < 14 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (O_TBL + 8 * m) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82340) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x82364 regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (O_TBL + 8 * m))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ H27 H10 H11 Hm HRA.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (E27 : ew (Ereg regs []) 27 = getr regs 27) by exact (ew_Ereg_nat regs _ 27 27%bv eq_refl).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 (8 * m))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HRA' : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (8 * m + O_TBL) 8)
  by (replace (8 * m + O_TBL) with (O_TBL + 8 * m) by lia; exact HRA).
assert (HS0 : st_ok rsegs (Ereg regs []) ss_OB0 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82340) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_OB0 f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E27, E10, H27. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    replace (8 * m) with (m * 8) by lia. rewrite Z.mod_mul by lia.
    unfold SHADOW_OFF, E0SB. repeat split; lia. }
assert (HS : st_ok rsegs (Ereg regs []) ss_OB (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82340) memc (seg_rom rsegs)))).
{ exact (st_ok_pin_lit rsegs _ _ _ 11%bv O_TBL HS0 eq_refl H11). }
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK E0Bspan 0x82364.
- (* the shadow obligation of the table entry *)
  cbn [ms_mem mkst]. unfold E0Bx.
  rewrite (U_atom _ 27 SHADOW_OFF) by first [rewrite E27, H27; reflexivity | unfold SHADOW_OFF; lia].
  rewrite U_SOff, E10. rewrite unsigned_lit_small by lia.
  rewrite zcanon_id by (unfold O_TBL, M64; lia). exact HRA'.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (E10' : ew Ev 10 = Z_to_bv 64 (8 * m))
        by (assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE;
            try rewrite (proj1 HA' 10%nat ltac:(lia)); exact E10) end.
    o_reg HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
    rewrite U_SOff, E10'. rewrite unsigned_lit_small by lia.
    rewrite zcanon_id by (unfold O_TBL, M64; lia). unfold O_TBL. lia.
Qed.

(* ======================== run C: 0x82364 -> 0x41c18 (the strlen wrapper) ======================== *)
Definition ss_OC : sstate :=
mkSS 0x82364 sr_atoms [YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [] [] []).

Lemma o_runC : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) a o,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 a -> 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) a 8 o ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82364) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k E0_STRLEN regs memc mdc [1; 10; 20; 21]%bv (fun _ => False)
(fun regs2 _ => getr regs2 20 = w64 o /\ getr regs2 10 = w64 o /\ getr regs2 21 = getr regs 6 /\
  getr regs2 1 = w64 0x82374)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs a o HJ H10 Ha0 Ha8 Ho Hval.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (B10 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 o]) 10) = a)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs [Z_to_bv 64 o]) 32 = Z_to_bv 64 o) by exact (ew_Ereg_extra regs [Z_to_bv 64 o] 0).
assert (D32 : sv_denot (Ereg regs [Z_to_bv 64 o]) (SOff 32 0) = Z_to_bv 64 o).
{ apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 o]) ss_OC (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82364) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_ro_region rsegs _ (w_H W) memc 10%nat a 0 8); [exact B10 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ a 0 8 (SOff 32 0) o);
      [exact D32 | change (8 * Z.of_N 8) with 64; lia | cbn; lia | rewrite Z.add_0_r; exact Hval].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs [Z_to_bv 64 o]) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 o]) (Ereg regs [Z_to_bv 64 o])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK E0Bspan E0_STRLEN.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [Z_to_bv 64 o] (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs [Z_to_bv 64 o]) Ev) by env_agree_chain HAE end.
    split; [|split; [|split]].
    * o_reg HS (20%bv : bv 5). exact D32.
    * o_reg HS (10%bv : bv 5). exact D32.
    * o_reg HS (21%bv : bv 5). exact (o_agree_atom regs [Z_to_bv 64 o] _ 6 6%bv HA' ltac:(lia) eq_refl).
    * o_reg HS (1%bv : bv 5). reflexivity.
Qed.

(* ======================== run D: 0x82374 -> 0x51d8c (__asan_memcpy) ======================== *)
Definition ss_Opc (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma o_runD : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 n -> 0 <= n -> n + 1 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82374) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k E0_MEMCPY regs memc mdc [1; 10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 12 = w64 (n + 1) /\ getr regs2 10 = getr regs 18 /\ getr regs2 11 = getr regs 20 /\
  getr regs2 1 = w64 0x82384)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HJ H10 Hn0 Hn1.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x82374) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82374) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK E0Bspan E0_MEMCPY.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE end.
    split; [|split; [|split]].
    * o_reg HS (12%bv : bv 5). cbn [sv_denot].
      try rewrite (proj1 HA' 10%nat ltac:(lia)). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * o_reg HS (10%bv : bv 5). exact (o_agree_atom regs [] _ 18 18%bv HA' ltac:(lia) eq_refl).
    * o_reg HS (11%bv : bv 5). exact (o_agree_atom regs [] _ 20 20%bv HA' ltac:(lia) eq_refl).
    * o_reg HS (1%bv : bv 5). reflexivity.
Qed.

(* ======================== run E: 0x82384 -> G 0x81afc ======================== *)
Lemma o_runE : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82384) memc (seg_rom rsegs)) mdc)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81afc regs memc mdc [6]%bv (fun _ => False)
(fun regs2 _ => getr regs2 6 = getr regs 21)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x82384) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82384) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs E0Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok o_tbl_ok HS HJ SHOK E0Bspan 0x81afc.
- awr_ok_tac.
- eapply (cb_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | exact HG | ].
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (cb_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [o_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE end.
    o_reg HS (6%bv : bv 5). exact (o_agree_atom regs [] _ 21 21%bv HA' ltac:(lia) eq_refl).
Qed.
End d.

(* ======================== the memory facts of the walk ======================== *)
(* a run's memory clause with an empty write set holds at every address *)
Lemma o_all_eq : forall (W : world rsegs) m m',
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
forall a, aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a.
Proof.
intros W m m' K a.
assert (Hm : forall mem, aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem (a mod 2 ^ 64))
  by (intros mem; unfold aview, mbyte; rewrite Z_to_bv_mod64; reflexivity).
rewrite (Hm m'), (Hm m). apply K; [apply Z.mod_pos_bound; lia | tauto].
Qed.

(* the bytes a string fact reads lie below the stack and the high shadow *)
Lemma o_strz_low : forall x (s : list byte) a, 0 <= x -> x + Z.of_nat (length s) + 8 <= O_SHI ->
cb_strz x s a -> 0 <= a < 2 ^ 40.
Proof.
intros x s a Hx Hs [Ha|Ha]; unfold O_SHI in *; [lia|].
unfold cb_hull, shadow_addr, SHADOW_OFF in Ha.
set (L := Z.of_nat (length s)) in *.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (P2 : (x + (L + 1) - 1) / 8 <= x + L) by (apply Z.div_le_upper_bound; lia).
assert (P3 : 0 <= (0x7fff8000 + x / 8) / 8) by (apply Z.div_pos; lia).
assert (P4 : 8 * ((0x7fff8000 + (x + (L + 1) - 1) / 8) / 8) <= 0x7fff8000 + (x + (L + 1) - 1) / 8)
  by (apply Z.mul_div_le; lia).
lia.
Qed.

(* the strlen / memcpy source premise from the string's facts *)
Lemma o_src_ok : forall (W : world rsegs) m R x s (regs : bvmap 5 word),
cb_strok W m R x s -> spZ regs = R -> src_ok rsegs W regs m x (Z.of_nat (length s) + 1).
Proof.
intros W m R x s regs (H0 & H1 & H2 & Hb & Hn & Ht & Hs & Ha & Hr & Hh) Hsp a Ha'.
assert (ESTACK = 4096) as Hes by reflexivity.
split.
- destruct (Z_lt_le_dec a (x + Z.of_nat (length s))) as [Hl|Hg].
  + destruct (Hb (Z.to_nat (a - x)) ltac:(lia)) as [E _]. rewrite Z2Nat.id in E by lia.
    replace (x + (a - x)) with a in E by lia. rewrite E. discriminate.
  + replace a with (x + Z.of_nat (length s)) by lia. rewrite Hn. discriminate.
- rewrite Hsp. intros Hin. apply (Hs a ltac:(lia)). lia.
Qed.

(* the string and its NUL as bytes *)
Lemma o_strok_bytes : forall (W : world rsegs) m R x s,
cb_strok W m R x s -> hm_bytes rsegs (w_H W) m x (s ++ [Cursor.NUL]).
Proof.
intros W m R x s (_ & _ & _ & Hb & Hn & _). apply hm_bytes_aview. intros i Hi.
rewrite length_app in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
- rewrite app_nth1 by exact Hl. exact (proj1 (Hb i Hl)).
- assert (i = length s) as -> by lia. rewrite nth_middle. rewrite Hn. reflexivity.
Qed.

(* ch's shadow hull lies in the frame's 116 shadow bytes *)
Lemma o_hull_ch : forall (rd : reader) F n,
(forall i, 0 <= i < 116 -> rd (shadow_addr F + i) <> None) -> F mod 8 = 0 -> 0 <= F -> 1 <= n <= 24 ->
shadow_hull_vis rd (F + 0xa0) n.
Proof.
intros rd F n Hp HF8 HF0 Hn s Hs. unfold shadow_addr in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
set (q := F / 8) in *.
assert (E1 : (F + 0xa0) / 8 = q + 20).
{ rewrite DF. replace (8 * q + 0xa0) with (q * 8 + 20 * 8) by lia. rewrite Z.div_add by lia.
  rewrite Z.div_mul by lia. reflexivity. }
assert (E2 : (F + 0xa0 + n - 1) / 8 <= q + 23).
{ apply Z.div_le_upper_bound; lia. }
assert (E3 : q + 20 <= (F + 0xa0 + n - 1) / 8).
{ apply Z.div_le_lower_bound; lia. }
rewrite E1 in Hs.
pose proof (Z.div_mod (SHADOW_OFF + (q + 20)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + 20)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (F + 0xa0 + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (F + 0xa0 + n - 1) / 8) 8 ltac:(lia)) as M2.
replace s with (SHADOW_OFF + q + (s - (SHADOW_OFF + q))) by lia.
apply Hp. unfold SHADOW_OFF in *. lia.
Qed.

(* ======================== the walk ======================== *)
Section w.
Variable B : asyms.
Hypothesis ASTRLEN : astrlen_realizes rsegs B E0_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy E0_MEMCPY.

(* the state at G: the journal, the I/O state, the callee-saved registers but s4 and s5, t1 kept, every byte
   outside the callees' stack and ch's len + 1 bytes, and ch holding odd_ch[c mod 14] with its NUL *)
Definition o_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(k : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (R F c : Z) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs 0x81afc regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io md md2 /\
(forall r, acallee_saved r -> r <> 20 -> r <> 21 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
getr regs2 6 = getr regs 6 /\
cb_kept W mem mem2 (fun a => (R - 2 * ESTACK <= a < R) \/ (F + 0xa0 <= a < F + 0xa0 + o_len (c mod 14) + 1)) /\
hm_bytes rsegs (w_H W) mem2 (F + 0xa0) (o_str (c mod 14) ++ [Cursor.NUL]).

Lemma o_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R F pos c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 13 = w64 c -> getr regs 18 = w64 (F + 0xa0) ->
200 <= c < 256 ->
R mod 16 = 0 -> R + 0x220 <= sp0 -> sp0 - STK <= R - T_SEG_STK ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
hd_fsh rsegs (w_H W) mem F (hmu_sh true true false false false true false false) ->
rom_view rsegs W mem ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (O_TBL + 8 * (c mod 14)) 8 ->
val_mem rsegs (mrestrict (w_H W) mem) (O_TBL + 8 * (c mod 14)) 8 (o_ptr (c mod 14)) ->
hd_cstr rsegs (w_H W) mem (o_ptr (c mod 14)) (map (fun b : byte => bv_unsigned b) (o_str (c mod 14))) ->
SRr rsegs W (cfg_at rsegs O_PC regs mem md) (o_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k regs mem md R F c).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R F pos c
  HJ H2 H3 H4 H27 H13 H18 Hc HR16 HRS HRSTK Hown HF Hfsh Hrom Hra Hcell Hcs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W mem md 4 pos HAR Hin4) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS lyc Sc W mem md 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HF in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFapp, HFceil.
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
rewrite Hts in HRSTK.
assert (HRlo : alloc_ceiling + 16384 <= R) by lia.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in HF32; [|lia]. destruct HF32 as [z Hz]. rewrite Hz. replace (z * 32) with ((4 * z) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (Hshf : shadow_addr F + 116 <= R - 2 * ESTACK)
  by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert (Hm : 0 <= c mod 14 < 14) by (apply Z.mod_pos_bound; lia).
remember (c mod 14) as m eqn:Em.
pose proof (o_ptr_lo m Hm) as (Hx0 & Hx1). pose proof (o_len_le m Hm) as Hl21.
assert (Hlen : o_len m = Z.of_nat (length (o_str m))) by reflexivity.
assert (Hok : cb_strok W mem R (o_ptr m) (o_str m)).
{ apply e0_strok_cstr; [exact Hcs | | lia].
  unfold O_SLO, O_SHI in *. rewrite <- Hlen. lia. }
(* ---- run A ---- *)
eapply SRr_bind.
{ unfold cfg_at, w64. exact (o_runA B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs c HJ H13 Hc Hrom). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & _ & H1a & H1b).
pose proof (o_all_eq W mem m1 Hm1) as A1.
(* ---- run B ---- *)
eapply SRr_bind.
{ refine (o_runB B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 d1 k r1 m HJ1 _ _ H1b Hm _).
  - o_keep Hk1. exact H27.
  - rewrite Em. exact H1a.
  - apply (cb_ra_kept W mem m1 _ 8 Hra); [unfold O_TBL; lia | intros a _; apply A1]. }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & _ & H2a).
pose proof (o_all_eq W m1 m2 Hm2) as A2.
(* ---- run C ---- *)
eapply SRr_bind.
{ refine (o_runC B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 d2 k r2 (O_TBL + 8 * m) (o_ptr m) HJ2 H2a _ _ _ _);
    [unfold O_TBL; lia | unfold O_TBL; lia
    | unfold O_SLO in Hx0; unfold O_SHI in Hx1; rewrite Hlen in Hx1; lia |].
  eapply val_mem_kept; [|exact Hcell]. intros j _. rewrite A2, A1. reflexivity. }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & _ & H3a & H3b & H3c & H3d).
pose proof (o_all_eq W m2 m3 Hm3) as A3.
assert (R3_2 : getr r3 2 = w64 R) by (o_keep Hk3; o_keep Hk2; o_keep Hk1; exact H2).
assert (R3_3 : getr r3 3 = w64 (as_gp B)) by (o_keep Hk3; o_keep Hk2; o_keep Hk1; exact H3).
assert (R3_4 : getr r3 4 = w64 (as_tp B)) by (o_keep Hk3; o_keep Hk2; o_keep Hk1; exact H4).
assert (HR47 : R < 2 ^ 47) by lia.
assert (Hsp3 : spZ r3 = sp0 + (R - sp0)) by (unfold spZ; rewrite R3_2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hok3 : cb_strok W m3 R (o_ptr m) (o_str m)).
{ eapply cb_strok_kept; [exact Hok|]. intros a _. rewrite A3, A2, A1. reflexivity. }
assert (Hrom3 : rom_view rsegs W m3).
{ intros a Ha. rewrite A3, A2, A1. exact (Hrom a Ha). }
assert (Hmod : (R - sp0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hal16; reflexivity).
pose proof Hok3 as (Ok0 & Ok1 & Ok2 & _ & _ & Okt & Oks & Oka & Okr & Okh).
(* ---- the strlen wrapper ---- *)
eapply SRr_bind.
{ refine (e0_strlen_at B LAWS E0_STRLEN ASTRLEN W r3 m3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc d3 k
    (o_ptr m) (o_len m) (R - sp0) (w64 0x82374) HJ3 H3b Ok0 _ _ _ Hsp3 Hmod _ _ R3_3 R3_4 H3d _ _ _ _ _ _ _ _ _).
  - lia.
  - rewrite Hlen. exact Ok1.
  - rewrite Hlen. exact Ok2.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - rewrite Hlen. exact (cb_strok_first_byte W m3 R _ _ Hok3).
  - rewrite Hlen. apply (o_src_ok W m3 R _ _ r3 Hok3). rewrite Hsp3. lia.
  - intros a Ha. replace (sp0 + (R - sp0)) with R by lia. apply Oks. rewrite <- Hlen. exact Ha.
  - rewrite Hlen. exact Oka.
  - rewrite Hlen. exact Okr.
  - rewrite Hlen. exact Okh.
  - rewrite Hlen. exact Okt.
  - intros a Ha _ _. exact (Hrom3 a Ha). }
intros W4 c4 _ (-> & r4 & m4 & d4 & -> & HJ4 & Hio4 & Hpr4 & H4a & Hm4 & _).
(* ---- run D ---- *)
eapply SRr_bind.
{ refine (o_runD B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m4 d4 k r4 (o_len m) HJ4 H4a _ _); rewrite Hlen; lia. }
intros W5 c5 _ (-> & r5 & m5 & d5 & -> & HJ5 & Hio5 & Hk5 & Hm5 & _ & H5a & H5b & H5c & H5d).
pose proof (o_all_eq W m4 m5 Hm5) as A5.
assert (R5 : forall r, acallee_saved r -> r <> 20 -> r <> 21 -> getr r5 (Z_to_bv 5 r) = getr r3 (Z_to_bv 5 r)).
{ intros r Hr H20 H21. rewrite (o_cs_kept r4 r5 _ Hk5 ltac:(o_clob) r Hr H20 H21). exact (Hpr4 r Hr). }
assert (R5_2 : getr r5 2 = w64 R)
  by (refine (eq_trans (R5 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R3_2).
assert (R5_3 : getr r5 3 = w64 (as_gp B))
  by (refine (eq_trans (R5 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R3_3).
assert (R5_4 : getr r5 4 = w64 (as_tp B))
  by (refine (eq_trans (R5 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) _); exact R3_4).
assert (R5_10 : getr r5 10 = w64 (F + 0xa0)).
{ refine (eq_trans H5b _). refine (eq_trans (Hpr4 18 ltac:(unfold acallee_saved; lia)) _).
  o_keep Hk3. o_keep Hk2. o_keep Hk1. exact H18. }
assert (R5_11 : getr r5 11 = w64 (o_ptr m)).
{ refine (eq_trans H5c _). refine (eq_trans (Hpr4 20 ltac:(unfold acallee_saved; lia)) _). exact H3a. }
assert (Hsp5 : spZ r5 = sp0 + (R - sp0)) by (unfold spZ; rewrite R5_2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (K53 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 2 * ESTACK <= a < R) -> aview rsegs (w_H W) m5 a = aview rsegs (w_H W) m3 a).
{ intros a Ha Hn. rewrite A5. apply Hm4; [exact Ha|]. replace (sp0 + (R - sp0)) with R by lia. exact Hn. }
assert (Hok5 : cb_strok W m5 R (o_ptr m) (o_str m)).
{ eapply cb_strok_kept; [exact Hok3|]. intros a Ha.
  pose proof (o_strz_low (o_ptr m) (o_str m) a ltac:(lia) ltac:(rewrite <- Hlen; unfold O_SHI in *; lia) Ha) as Hal.
  apply K53; lia. }
assert (Hfsh5 : hd_fsh rsegs (w_H W) m5 F (hmu_sh true true false false false true false false)).
{ eapply hm_fsh_kept; [exact Hfsh|]. rewrite hmu_sh_len. intros i Hi.
  assert (0 <= shadow_addr F) by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)); lia).
  rewrite K53 by lia. rewrite A3, A2, A1. reflexivity. }
pose proof Hok5 as (Pk0 & Pk1 & Pk2 & _ & _ & _ & Pks & Pka & Pkr & Pkh).
assert (Hn22 : 1 <= o_len m + 1 <= 22) by (rewrite Hlen; lia).
(* ---- __asan_memcpy (ch, o, len + 1) ---- *)
eapply SRr_bind.
{ refine (e0_memcpy_at B LAWS AMEMCPY W r5 m5 STK sp0 FP ly S W0 mem0 md0 own lyc Sc d5 k (F + 0xa0) (o_ptr m)
    (o_len m + 1) (R - sp0) (w64 0x82384) HJ5 R5_10 R5_11 H5a _ _ _ Hsp5 Hmod _ _ R5_3 R5_4 H5d _ _ _ _ _ _ _ _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + right; right; right. exists 4, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
      rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + lia.
  - unfold amem_range. destruct HFapp as [_ [HL | [HH1 HH2]]].
    + left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
    + right. unfold ASAN_CEIL, kHighMemEnd in *. lia.
  - replace (F + 0xa0) with (F + HMU_CH + 0) by (unfold HMU_CH; lia).
    apply (hmu_B_ra_ch rsegs _ _ F true false false false true false false 0 (o_len m + 1) Hfsh5 HF8); lia.
  - intros _. apply (o_hull_ch _ F (o_len m + 1)); [| exact HF8 | lia | lia].
    intros i Hi. rewrite (Hfsh5 i ltac:(rewrite hmu_sh_len; lia)). discriminate.
  - lia.
  - lia.
  - rewrite Hlen. apply (o_src_ok W m5 R _ _ r5 Hok5). rewrite Hsp5. lia.
  - destruct (Z_le_gt_dec (o_ptr m + (o_len m + 1)) (F + 0xa0)) as [Hle|Hgt]; [right; exact Hle|].
    destruct (Z_le_gt_dec (F + 0xa0 + (o_len m + 1)) (o_ptr m)) as [Hle'|Hgt']; [left; exact Hle'|].
    exfalso.
    apply (frm_img rsegs B LAWS lyc Sc W mem md 4 pos (Z.max (F + 0xa0) (o_ptr m)) HAR Hin4).
    + rewrite <- HF. change (fs_frame_bytes 4) with 1024. lia.
    + apply o_str_img. unfold O_SLO, O_SHI in *. lia.
  - unfold amem_range. left. unfold kLowMemEnd, O_SLO, O_SHI in *. lia.
  - rewrite Hlen. exact Pkr.
  - intros _. rewrite Hlen. exact Pkh. }
intros W6 c6 _ (-> & r6 & m6 & d6 & -> & HJ6 & Hio6 & Hpr6 & _ & Hcp6 & Hm6 & _).
(* ---- run E ---- *)
eapply SRr_mono.
{ exact (o_runE B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m6 d6 k r6 HJ6). }
intros W7 c7 _ (-> & r7 & m7 & d7 & -> & HJ7 & Hio7 & Hk7 & Hm7 & _ & H7a).
pose proof (o_all_eq W m6 m7 Hm7) as A7.
unfold o_post. rewrite <- Em.
split; [reflexivity|]. exists r7, m7, d7.
split; [reflexivity|].
split; [exact HJ7|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [exact Hio2|]. eapply same_io_trans; [exact Hio3|].
  eapply same_io_trans; [exact Hio4|]. eapply same_io_trans; [exact Hio5|]. eapply same_io_trans; [exact Hio6|].
  exact Hio7. }
split.
{ intros r Hr H20 H21.
  rewrite (o_cs_kept r6 r7 _ Hk7 ltac:(o_clob) r Hr H20 H21), (Hpr6 r Hr), (R5 r Hr H20 H21),
    (o_cs_kept r2 r3 _ Hk3 ltac:(o_clob) r Hr H20 H21), (o_cs_kept r1 r2 _ Hk2 ltac:(o_clob) r Hr H20 H21),
    (o_cs_kept regs r1 _ Hk1 ltac:(o_clob) r Hr H20 H21).
  reflexivity. }
split.
{ refine (eq_trans H7a _).
  refine (eq_trans (Hpr6 21 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans (Hk5 21%bv ltac:(first [cbv; discriminate | o_notin])
                              ltac:(first [cbv; discriminate | o_notin])) _).
  refine (eq_trans (Hpr4 21 ltac:(unfold acallee_saved; lia)) _).
  refine (eq_trans H3c _).
  refine (eq_trans (o_t1_kept r1 r2 _ Hk2 ltac:(o_clob)) _).
  exact (o_t1_kept regs r1 _ Hk1 ltac:(o_clob)). }
split.
{ intros a Ha Hn.
  assert (N1 : ~ (F + 0xa0 <= a < F + 0xa0 + (o_len m + 1))) by (intros X; apply Hn; right; lia).
  assert (N2 : ~ (sp0 + (R - sp0) - ESTACK <= a < sp0 + (R - sp0))) by (intros X; apply Hn; left; lia).
  assert (N3 : ~ (R - 2 * ESTACK <= a < R)) by (intros X; apply Hn; left; exact X).
  rewrite A7, (Hm6 a Ha N1 N2), (K53 a Ha N3), A3, A2, A1. reflexivity. }
eapply hm_bytes_kept; [| intros x _; apply A7].
apply (hm_memcpy_bytes rsegs (w_H W) m5 (w_H W) m6 (o_ptr m) (F + 0xa0)).
- exact (o_strok_bytes W m5 R _ _ Hok5).
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hcp6. rewrite Hlen. lia.
Qed.
End w.
End b.

Print Assumptions o_walk.
