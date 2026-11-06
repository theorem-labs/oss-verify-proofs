(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Jb0RegionPoisoned Jb0AsanMemset Jb0AsanMemcpy Jb0StrlenIcpt Jb0TlsGetAddr Jb0FakeStack1 Jb0FakeStackGC Jb0Fsm4Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0Fsm4Gen () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Fsm4Core."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3word_to_le_bytes"; "4bvmap"; "0M2"; "0Mj"; "5msteps"; "6core4_mem"]; ["7keeps_but"; "8getr"; "8mkst"; "8rdn"; "9keeps_cs"; ":mem_grows"; ";loaded_segments"; "<le"; "<lt"; "<sub"; "0a0v"; "0ff"; "0fs"; "0fx"; "0h"; "0j"]; ["0mem0"; "0pos"; "0r2"; "0ra"; "0regs"; "0regs'"; "0rom"; "0s"; "0sp"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0tpv"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
try change (2 ^ 7)%Z with 128%Z; first [reflexivity | f_equal; lia].
Section PRE4.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra a0v : word.
Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hret : ret_ok ra.
Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
Hypothesis Hmd : (0 <= md < 255)%Z.
Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
Hypothesis Hverb : (0 <= verb < 3)%Z.
Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
tls_cells tpv 0x135198 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
Variable fs : Z.
Definition tls_rp : Z := tls_res off ent.
Hypothesis Hfs0 : (0 < fs < 2 ^ 64)%Z.
Hypothesis Hr : (0 <= tls_rp /\ tls_rp + 8 < 2 ^ 64)%Z /\ (tls_rp + 8 <= s - 208 \/ s <= tls_rp)%Z.
Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_rp) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
Definition F4p (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).
Lemma sp_sp4 : ltac2:(TCodec.tc2 tcn__Jb0Fsm4Gen "9'7'Q;yR0%211vQ8&Q:vQ7%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Section SE.
Local Abbreviation SEC_T_fsm4_pre_run := (ltac2:(TCodec.tc2 tcn__Jb0Fsm4Gen "U0&;y5'Q;yR0%211%5241'7&Ar1(Q9+:(5%33;21%6251vJ%93;21r2+4%93A17%<231&Q:vQ=%22C1%A3C41r3+2%A3I1?%D231vQ8%G3I21r4+1%G3O1E%J231vQ3%M3O21'8'4y8%Q511%311p0Q51'6'>&F&BvMr7+[fj8%Q83Q>1Q6/01Q>vQ0vQ6%8576321+[fkD%Q>3QD1Q</01QD%<5;Q91QA5%?3>51+9%QC3QK1QA%QF2Q=1vL%Q;2QL1%QJ3QL31+8%QI3R11QG%QL2QC1vQ7%QA2R21%R03R231%R02QGQ=&I+Q0%2261%QG2R81%R63R851&@(1%R=1R>+B%R83R@1R6(3%114%63531%736I1%837D1%938QM1%:39QH1%<31Q:R9'9&H&Q<%12RJRE+V@%G2K1%5231&G%12N5%9231%R<1RD%QB1RE%S03QN21p041pRNS41&E%12QGS2'2%11R5%R811&C%Q72Q;Q>%RL2S=1u8%44R6S:21(0&:%124RC%32:1%SA3:51+@%QA2QE1%S62SG1%=4R?SC1:%SE2R=QJ%92<1%;2B1%SI3B41+H%QI2QM1%S>2SO1%E4RGSK1B%SM2RER8%A2D1%C2J1%T13J41%J4RLT0QMG%T22RJQH%F2I1%H2O1%T63O41%S3261%S42?1%S52H1%S62Q61%S72Q91%S82QI1%S92R71%S:2R>1%S;2RE1%S<2RL1qJS>1%SD2S?1qR6TD1%SF2TE1p0SH1p0SO1p0T61p0T?1pR:TJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_fsm4_pre_run) 0%nat 0%nat).
Theorem fsm4_pre_run : ltac:(sec_stmt2 constr:(SEC_T_fsm4_pre_run) 1%nat 0%nat).
Proof.
intros H10 H4 H2 H1.
rewrite sp_sp4 in H2. destruct Hr as (R1 & R2).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x5db48 : word) mem0 rom) (mkst r1 (0x62d68 : word) (F4p regs) rom)
/\ (getr r1 10 = Z_to_bv 64 0x135198 /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 2 = Z_to_bv 64 (s - 32)
/\ getr r1 1 = (0x5db6c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
{ unfold F4p. eexists. split.
- stepiv (ltac:(oF' 0x5db48%Z)) (ltac:(oD' 0x5db48%Z)) (Z_to_bv 64 (s - 32)) ltac:(wval).
stepsd (ltac:(oF' 0x5db4c%Z)) (ltac:(oD' 0x5db4c%Z)) (Z_to_bv 64 (s - 8)) ra
ltac:(apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepsd (ltac:(oF' 0x5db50%Z)) (ltac:(oD' 0x5db50%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8)
ltac:(apply (store_ok_mono _ _ mem0); [apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepsd (ltac:(oF' 0x5db54%Z)) (ltac:(oD' 0x5db54%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9)
ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepsd (ltac:(oF' 0x5db58%Z)) (ltac:(oD' 0x5db58%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18)
ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; [eapply mem_grows_trans; apply wbytes_grows | apply wbytes_grows]|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
stepiv (ltac:(oF' 0x5db5c%Z)) (ltac:(oD' 0x5db5c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepn (ltac:(oF' 0x5db60%Z)) (ltac:(oD' 0x5db60%Z)).
stepn (ltac:(oF' 0x5db64%Z)) (ltac:(oD' 0x5db64%Z)).
stepn (ltac:(oF' 0x5db68%Z)) (ltac:(oD' 0x5db68%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN4 & Q10 & Q4 & Q8 & Q2 & Q1 & K1).
assert (Hra : ret_ok (0x5db6c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hrb : ret_ok (0x5d7b8 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (OF4 : forall x : word, (bv_unsigned x < s - 32 \/ s <= bv_unsigned x)%Z -> F4p regs x = mem0 x).
{ intros x Hx. unfold F4p. pose proof (u64_range x).
destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
| rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
destruct (wrap_tls_get_addr_run (F4p regs) rom (Z_to_bv 64 (s - 32)) (0x5db6c : word) (s - 32) tpv 0x135198 md off dtv ent key tsd ctx th tb te F V verb dto blk rec
ltac:(unorm; reflexivity) Hra ltac:(lia)
ltac:(replace (s - 32 - 176)%Z with (s - 208)%Z by lia; apply (store_ok_mono _ _ mem0); [unfold F4p; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia])
Htp ltac:(lia) Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec
ltac:(intros M' HM'; apply HC0; intros x Hx; rewrite (HM' x) by lia; apply OF4; lia)
r1 Q10 Q4 Q2 Q1) as (r2 & M2 & RUN2 & T10 & T2 & T1 & K2 & O2 & G2).
replace (s - 32 - 176)%Z with (s - 208)%Z in O2 by lia.
fold tls_rp in T10.
assert (O2' : forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M2 x = mem0 x).
{ intros x Hx. rewrite (O2 x) by lia. apply OF4. lia. }
assert (T8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
assert (EQ : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
rdn ASEGS M2 (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
{ intros a k Ha Hk1 Hk2. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O2'. lia. }
pose proof HRfs as C0. rewrite <- (EQ tls_rp 8%nat) in C0 by (cbn [Z.of_nat Pos.to_nat]; lia).
assert (G2' : mem_grows mem0 M2).
{ eapply mem_grows_trans; [|exact G2]. unfold F4p. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk. assert (Hk' : (8 <= k <= 32)%Z) by lia.
rewrite (rdn_ext ASEGS 8 M2 (F4p regs)); [| unorm; cbn; lia |].
- unfold F4p. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
apply rdn_wbytes_hit8; unorm; lia.
- intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply O2. lia. }
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5db6c : word) M2 rom) (mkst r3 (0x5db74 : word) M2 rom)
/\ (getr r3 9 = Z_to_bv 64 fs /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
{ eexists. split.
- chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact (ltac:(oF' 0x5db6c%Z)) | reflexivity | exact (ltac:(oD' 0x5db6c%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 tls_rp) by (symmetry; wv2) end; exact C0 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].
stepb_ft (ltac:(oF' 0x5db70%Z)) (ltac:(oD' 0x5db70%Z)) ltac:(cond).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
destruct S3 as (r3 & RUN3 & U9 & U8 & U2 & K3).
exists r3, M2. split; [eapply msteps_trans; [exact RUN4|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
split; [exact U9|]. split; [exact U8|]. split; [exact U2|].
split. { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2 | exact K3]. }
split; [exact O2'|]. split; [exact G2'|].
repeat split; apply SL; [left | right; left | right; right; left | right; right; right]; split; reflexivity.
Qed.
End SE.
Variables h j pos ff : Z.
Hypothesis Hfs : (0x693000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
Hypothesis Hj : (0 <= j < 1024)%Z.
Hypothesis Hpos_def : pos = ((h + j) mod 1024)%Z.
Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 4194304 + 1024 * pos)%Z.
Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 30720 + (h + i) mod 1024)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z.
Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 30720 + pos)) 1%nat = Some [Z_to_bv 8 0].
Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
Hypothesis HG : rt_layout_globs mem0.
Hypothesis Happ : in_app ff.
Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 128%nat = true.
Hypothesis Hshadow_dj : (SB + ff / 8 + 128 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 128 <= 0x1343a0 \/ 0x13d738 <= SB + ff / 8)%Z.
Section SE.
Local Abbreviation SEC_T_fsm4_gen_run := (ltac2:(TCodec.tc2 tcn__Jb0Fsm4Gen "S:&;y5'Q;yR0%211%5241'7&Ar1(Q9+:(5%33;21%6251vJ%93;21r2+4%93A17%<231&Q:vQ=%22C1%A3C41r3+2%A3I1?%D231vQ8%G3I21r4+1%G3O1E%J231vQ3%M3O21'8'4y8%Q511%311p0Q51'6'>&F&BvMr7+[fj8%Q83Q>1Q6/01Q>vQ0vQ6%8576321&?vQ7vLvNvOvQ1vK%77QE654321%A5@Q>L1:%D3C:1%QI2Q@QD%Q=2QN5%QL3QN21%QL2QCQ9%QN3R01Q8%QN2QEQ5%R03R21Q4&D%12IQH'9&H&Q<%12R9R4&I+V@%22H1%6241&G%12K6%:231%QL1R4%Q21R5%R@3Q>21p041pRNRD1&E%12Q7RB%QA231%QB2D1%QC2G1%QD2J1%QE2M1%QF2Q11qLQH1%QN2QI1qR<RN1%R02RO1p0R21p0R91p0R@1p0RI1pR:S41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_fsm4_gen_run) 0%nat 0%nat).
Theorem fsm4_gen_run : ltac:(sec_stmt2 constr:(SEC_T_fsm4_gen_run) 1%nat 0%nat).
Proof.
intros H10 H4 H2 H1.
destruct (fsm4_pre_run regs H10 H4 H2 H1) as (r2 & M2 & RUNP & P9 & P8 & P2 & KP & O2 & G2 & SLOTS).
destruct Hfs as (Fs1 & Fs2 & Fs3). destruct Hshadow_dj as (SD1 & SD2).
pose proof (Z.mod_pos_bound (h + j) 1024 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 128 < 2 ^ 64)%Z).
{ unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
assert (EQ : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
rdn ASEGS M2 (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
{ intros a k Ha Hk1 Hk2. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O2. lia. }
pose proof Hng as C1. rewrite <- (EQ (fs + 96)%Z 1%nat) in C1 by (cbn [Z.of_nat Pos.to_nat]; lia).
pose proof Hssl as C2. rewrite <- (EQ (fs + 88)%Z 8%nat) in C2 by (cbn [Z.of_nat Pos.to_nat]; lia).
pose proof Hhint as C3. rewrite <- (EQ (fs + 32)%Z 8%nat) in C3 by (cbn [Z.of_nat Pos.to_nat]; lia).
pose proof Hflag as C4. rewrite <- (EQ (fs + 4096 + 30720 + pos)%Z 1%nat) in C4 by (cbn [Z.of_nat Pos.to_nat]; lia).
assert (CP : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS M2 (Z_to_bv 64 (fs + 4096 + 30720 + (h + i) mod 1024)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z).
{ intros i Hi. destruct (Hprobe i Hi) as (b & Rb & Bb). exists b. split; [|exact Bb]. pose proof (Z.mod_pos_bound (h + i) 1024 ltac:(lia)).
rewrite (EQ (fs + 4096 + 30720 + (h + i) mod 1024)%Z 1%nat) by (cbn [Z.of_nat Pos.to_nat]; lia). exact Rb. }
assert (GLM : rt_layout_globs M2).
{ destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
rewrite !(rdn_ext ASEGS _ M2 mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply O2; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
repeat split; assumption. }
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x5db74 : word) M2 rom) (mkst r3 (0x5db8c : word) M2 rom)
/\ (getr r3 9 = Z_to_bv 64 fs /\ getr r3 18 = Z_to_bv 64 20 /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
{ eexists. split.
- chain_step; [reflexivity | eapply step_lbu; [exact (ltac:(oF' 0x5db74%Z)) | reflexivity | exact (ltac:(oD' 0x5db74%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 96)) by (symmetry; wv2) end; exact C1] | step_simpl; vnorm].
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact (ltac:(oF' 0x5db78%Z)) | reflexivity | exact (ltac:(oD' 0x5db78%Z))
| match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 88)) by (symmetry; wv2) end; exact C2 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].
stepb (ltac:(oF' 0x5db7c%Z)) (ltac:(oD' 0x5db7c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
destruct S3 as (r3 & RUN3 & U9 & U18 & U8 & U2 & K3).
destruct SLOTS as (SL8 & SL16 & SL24 & SL32).
destruct (@fsm4_core_run fx M2 rom s fs h j pos ff ra (getr regs 8) (getr regs 9) (getr regs 18) Hret ltac:(lia) ltac:(lia) Hh Hj Hpos_def Hff_def C3 CP C4
ltac:(apply (store_ok_mono _ _ mem0 M2 _ G2); exact Hwfs) GLM Happ ltac:(apply (store_ok_mono _ _ mem0 M2 _ G2); exact Hshadow_ok) ltac:(lia)
ltac:(repeat split; assumption) r3 U9 U18 U8 U2) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & K4).
exists r4, M2. split; [eapply msteps_trans; [exact RUNP|]; eapply msteps_trans; [exact RUN3 | exact RUN4]|].
split; [exact Q10|]. split; [rewrite Q2; symmetry; apply sp_sp4|]. split; [exact Q1|].
split; [|split; [exact O2 | exact G2]].
assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r4) by (eapply keeps_but_trans; [exact KP|]; eapply keeps_but_trans; [exact K3 | exact K4]).
intros r Hcs. destruct (decide (r = 1%bv)) as [->|N1']; [rewrite Q1, H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2']; [rewrite Q2, H2; symmetry; apply sp_sp4|].
destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|].
apply KB; [exact Hcs|]. clear -N1' N2' N8 N9 N18. cbv. intuition congruence.
Qed.
End SE.
End PRE4.
End FPX_1.
