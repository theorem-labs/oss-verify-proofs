(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QYyZ QnRU QteI QMPy QIG5 QC9y Qr5k QbPx_c1 QCqp Qi1S Q0z1 QlES QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QYyZ.Mq2 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qr5k.Mq1 Qi1S.Mq1.
Import Q0z1.
Import QlES.
Import QXE1.Mq0. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase sn_write_entry 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
[C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition dapp (D dn : Z) : Prop := (0x645000 <= D /\ D + dn + 8 <= 0x7fff8000) \/ (0x10007fff8000 <= D /\ D + dn + 8 <= 2^47).

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells asegs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
rw_cells asegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells asegs m (Fp + 148) (snfile_rest CK) ->
rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
rw_cells asegs m D [CB dn junkd] ->
ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_model (OUT_sn) (OUTFP_sn) fmt args [] = Qc6I.Ret (Ok (r, o)) ->
fp_calls (length fmt) fmt args = [] ->
(length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) -> szone A (zlength fmt) ->
(q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^47) ->
(q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) ->
dapp D (Z.of_nat dn) -> (0 < zlength o -> rng_ok m D (zlength o)) ->
evt asegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd385c) fc None m (seg_rom asegs)).

Theorem vfprintf_sn_proof {BAND : Band} : vfprintf_sn_stmt.
Proof.
unfold vfprintf_sn_stmt. intros until o. cbv zeta.
intros -> -> -> FH FR CKC DST ISHm BY HF P1 VAA AOK MODEL FPC ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA HSZ QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 DAPP RD.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z m) as MU1.
unfold snfile_head, gfile_cells, sn_write_entry in FH. unfold snfile_rest in FR. unfold dapp in DAPP.

call vf_saves; [exact ST | lia | exact GLO | exact MI | exact SSP1 | exact SSP2 | ].
lazymatch goal with H : stk _ ?mm lo (bv_unsigned sp + -368) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -368) (C8 _ :: _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FRv end.
try rename MI0 into MI.

pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | exact HSZ | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. if_lit. zs. zs. if_lit. zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in *. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size csize Nat.add] in FB.

pose proof towrite_g_proof as TW. unfold towrite_g_stmt in TW.
eapply evt_cut.
{ eapply (TW _ _ _ _ _ _ _ _ _ (Z_to_bv 64 Fp)) with (flags := Z_to_bv 64 0) (rpos := 0) (rend := 0) (close := 0) (wend := 0) (wpos := 0) (wbase := 0)
(writefn := 889040) (seekfn := 0) (buf := bv_unsigned sp + -352) (bufsize := 80) (fd := 0) (mode := Z_to_bv 64 0) (lock := Z_to_bv 64 4294967295) (lbf := 4294967295);
rewrite ?unsigned_lit by lia; [ unfold gfile_cells; exact FH | reflexivity | lia | lia | lia | assumption ]. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FH').
rewrite !unsigned_lit in MUc, FH' by lia. clear FH.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.

set (B := bv_unsigned sp + -352) in *.
unfold gfile_cells in FH'.
apply (rw_cells_merge asegs _ _ [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in FH'.
apply (rw_cells_split_CB asegs _ _ [] _ _ _ [1; 31]%nat) in FH'; [|reflexivity].
apply (rw_cells_merge asegs _ _ [_; _; _; _]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 889040); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)]) in FH'.
cbn [app mk_CB_cells cells_size csize Nat.add] in FH'.
match type of FH' with rw_cells _ _ _ (CB 1 ?b1 :: CB 31 ?b31 :: _ :: _ :: CB 96 ?b96 :: _) =>
let v1 := eval vm_compute in b1 in change b1 with v1 in FH'; set (j1 := b31) in FH'; set (j2 := b96) in FH' end.

apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by (subst B; lia).
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).

assert (ISHc : forall mm, munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m mm -> wmono asegs m mm -> ISH mm).
{ intros mm MUx WMx. eapply ISH_munch_app; [exact ISHm | exact MUx | exact WMx |].
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SNK : SINK_sn Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368) mc []) end.
{ exists jb. split; [|split; [exact FR | split; [reflexivity | split; [unfold zlength, SN_CAP; rewrite LJB; reflexivity | unfold SN_CAP; split; [subst B; lia | split; [lia | split; [subst B; lia | split; [subst B; lia |]]]]]]]].
- unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB. rewrite !Z.add_0_r.
split; [unfold FILE_cells; exact FH'|].
split. { apply (proj2 (rw_cells_app asegs _ _ [CB 0 []] [CB 80 jb])). split; [apply rw_cells_CB0; subst B; lia|]. cbn [cells_size csize Nat.add]. rewrite Z.add_0_r. exact BUFc. }
split; [reflexivity|]. split; [vm_compute; discriminate|]. subst B; lia.
- apply ISHc; assumption. }

assert (PCALL : forall Q ms, implM asegs (printf_model OUT_sn OUTFP_sn fmt args) [] Q ms -> evt asegs (Q r o) ms).
{ intros Q ms H. unfold implM in H. rewrite MODEL in H. exact H. }
pose proof (printf_core_proof (list Z) Fp B 80 _ _ OUT_sn OUTFP_sn
(sn_sink_frame Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_sink_flags Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_topok (bv_unsigned sp + -368))
(sn_out Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))) as PC2.
unfold printf_core_stmt in PC2.
eapply evt_cut.
{ apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_sn, zlength.
all: try (subst B; lia). all: try exact I.
- exact SNK.
- exact BY.
- exact HF.
- reflexivity.
- exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- match goal with H : stk _ _ lo _ |- _ => exact H end.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- exact HSZ. }
cbv beta. intros ms' P. clear PC2 PCALL MODEL AOK HF BY VAA P1 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold INT_MAX in Hr.
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
fix_ret.

destruct SNK3 as (junk3 & WF3 & FR3 & FRL3 & LEN3 & SEPB3 & T13 & T23 & B473 & ISH3).
destruct WF3 as (FC3 & BUF3 & FL3 & LBF3 & B03 & BHI3 & SEPfb3).
pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength, SN_CAP in LEN3.
unfold FILE_cells in FC3. subst j2.
lazymatch type of FC3 with rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; CB 96 _; ?c6] =>
pose proof (rw_cells_unmerge mm Fp [c1; c2; c3; c4]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 889040); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)] [c6]) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
subst j1.
apply (rw_cells_merge asegs _ _ [] [CB 1 _; CB 31 _]) in FC3. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC3.
match type of FC3 with rw_cells _ _ _ (CB 32 ?b :: _) => let v := eval vm_compute in b in change b with v in FC3 end.
lazymatch type of FC3 with rw_cells _ ?mm _ (CB 32 _ :: ?rest) =>
pose proof (rw_cells_unmerge mm Fp [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
lazymatch type of UM with rw_cells _ _ _ (CB 32 ?b :: _) -> _ => let v := eval vm_compute in b in change b with v in UM end.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
zs. zs. zs. brf Kb; [exfalso; lia|].
zs. zs. zs. zs. zs.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] _)) in FC3. destruct FC3 as [F0 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F40 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F48 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F56 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FC3. destruct FC3 as [F64 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F88 F96]. cbn [cells_size csize Nat.add app] in F96.
replace (Fp + Z.of_nat 40)%Z with (Fp + 40)%Z in F40 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8)%Z with (Fp + 48)%Z in F48 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 56)%Z in F56 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 64)%Z in F64 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24)%Z with (Fp + 88)%Z in F88 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8)%Z with (Fp + 96)%Z in F96 by lia.
unfold snfile_rest in FR3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR3. destruct FR3 as [F148 FR3]. cbn [cells_size csize Nat.add app] in FR3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR3. destruct FR3 as [F152 F160]. cbn [cells_size csize Nat.add app] in F160.
replace (Fp + 148 + Z.of_nat 4)%Z with (Fp + 152)%Z in F152 by lia.
replace (Fp + 148 + Z.of_nat 4 + Z.of_nat 8)%Z with (Fp + 160)%Z in F160 by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ BUF3) as SRC3. cbn [cells_bytes cbytes app] in SRC3. rewrite app_nil_r in SRC3.
apply bytes_at_app in SRC3. destruct SRC3 as [SRC3 _].
replace (Z_to_bv 64 (B + Z.of_nat (length o))) with (Z_to_bv 64 (B + zlength o)) in F40 by reflexivity.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD3 : (0 < zlength o)%Z -> rng_ok mc D (zlength o))
end.
{ intros K. eapply rng_ok_munch; [exact (RD K) | exact MU | exact WM |].
pose proof (proj1 (proj2 (RD K))) as D47. unfold zlength in *.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
eapply evt_cut.
{ eapply sn_write_spec with (o := o) (B := B) (n := n) (D := D) (CK := CK) (dn := dn) (bufp := B) (Fp := Fp) (junk := junkd) (lo := lo);
rewrite ?unsigned_lit by lia; unfold zlength, SN_WRITE_STACK, MEMCPY_ICPT_STACK;
[ reflexivity | reflexivity | exact F40 | exact F56 | exact F88 | exact F152 | | exact SRC3 | | exact ROOM | lia | subst B; lia | subst B; lia
| match goal with H : stk _ _ lo _ |- _ => exact H end | exact GLO | lia | assumption
| subst B; lia | lia | lia | lia | lia | lia | subst B; lia | lia | subst B; lia | subst B; lia
| exact (proj2 (proj2 ISH3)) | exact (proj1 (proj2 ISH3))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH3)); [unfold szone; right; left; subst B; lia | lia]
| exact RD3 ].
all: lazymatch goal with |- rw_cells _ _ ?a _ => match goal with H : rw_cells _ _ a _ |- _ => exact H end end. }
cbv beta. intros ms' P.
unfold sn_write_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4 & CK4 & DST4 & F40' & F56' & SRC4).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
fix_ret.

zs. zs. zs. zs. zs.
zs. replace (0 <? B)%Z with true by (symmetry; apply Z.ltb_lt; subst B; lia). cbn [Z.b2z].
zs. zs. rewrite ?Z.lor_0_l. zs.
zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. zs. zs. zs. zs. rewrite ?Z.lor_0_l. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6565536 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.
try rewrite (land_M64_id r) by lia.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z [C8 apv] |- _ => rename H into APC4 end.
match goal with H : rw_cells _ ?mm B _ |- _ => rename H into BUF4 end.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
release_frame APC4 ST5 (bv_unsigned sp + -360)%Z.
release_frame AP2 ST5 B.
release_frame BUF4 ST5 (bv_unsigned sp + -272)%Z.
release_frame FRv ST5 (bv_unsigned sp).
lazymatch goal with F0 : rw_cells _ ?mm Fp _, F40 : rw_cells _ ?mm (Fp + 40)%Z _, F48 : rw_cells _ ?mm (Fp + 48)%Z _, F56 : rw_cells _ ?mm (Fp + 56)%Z _,
F64 : rw_cells _ ?mm (Fp + 64)%Z _, F88 : rw_cells _ ?mm (Fp + 88)%Z _, F96 : rw_cells _ ?mm (Fp + 96)%Z _,
F148 : rw_cells _ ?mm (Fp + 148)%Z _, F152 : rw_cells _ ?mm (Fp + 152)%Z _, F160 : rw_cells _ ?mm (Fp + 160)%Z _ |- _ =>
assert (FALL : rw_cells asegs mm Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 889040); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 bufp)]
++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode'; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)]
++ [C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 CK)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F0|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F40|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F48|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F56|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F64|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F88|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F96|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F148|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F152|];
piece F160
| ] end.
destruct (rw_cells_forget _ _ _ _ FALL) as [fjunk FJ]. cbn [cells_size csize Nat.add app] in FJ.
apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
split; [exact ST5|].
split; [split; [exact SSP1 | exact SSP2]|].
split; [exact DST4|]. split; [exact CK4|]. exact FJ.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbPx_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbPx_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi1S.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_6 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase sn_write_entry 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
[C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition dapp (D dn : Z) : Prop := (0x647000 <= D /\ D + dn + 8 <= 0x7fff8000) \/ (0x10007fff8000 <= D /\ D + dn + 8 <= 2^47).

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells asegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ rw_cells asegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells asegs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt {BAND : Band} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
rw_cells asegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells asegs m (Fp + 148) (snfile_rest CK) ->
rw_cells asegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
rw_cells asegs m D [CB dn junkd] ->
ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_model (OUT_sn) (OUTFP_sn) fmt args [] = Qc6I.Ret (Ok (r, o)) ->
fp_calls (length fmt) fmt args = [] ->
(length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) -> szone A (zlength fmt) ->
(q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^47) ->
(q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 <= 2^47) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) ->
dapp D (Z.of_nat dn) -> (0 < zlength o -> rng_ok m D (zlength o)) ->
evt asegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5f20) fc None m (seg_rom asegs)).

Theorem vfprintf_sn_proof {BAND : Band} : vfprintf_sn_stmt.
Proof.
unfold vfprintf_sn_stmt. intros until o. cbv zeta.
intros -> -> -> FH FR CKC DST ISHm BY HF P1 VAA AOK MODEL FPC ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA HSZ QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 DAPP RD.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z m) as MU1.
unfold snfile_head, gfile_cells, sn_write_entry in FH. unfold snfile_rest in FR. unfold dapp in DAPP.

call vf_saves; [exact ST | lia | exact GLO | exact MI | exact SSP1 | exact SSP2 | ].
lazymatch goal with H : stk _ ?mm lo (bv_unsigned sp + -368) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -368) (C8 _ :: _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FRv end.
try rename MI0 into MI.

pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | exact HSZ | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. if_lit. zs. zs. if_lit. zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in *. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size csize Nat.add] in FB.

pose proof towrite_g_proof as TW. unfold towrite_g_stmt in TW.
eapply evt_cut.
{ eapply (TW _ _ _ _ _ _ _ _ _ (Z_to_bv 64 Fp)) with (flags := Z_to_bv 64 0) (rpos := 0) (rend := 0) (close := 0) (wend := 0) (wpos := 0) (wbase := 0)
(writefn := 898964) (seekfn := 0) (buf := bv_unsigned sp + -352) (bufsize := 80) (fd := 0) (mode := Z_to_bv 64 0) (lock := Z_to_bv 64 4294967295) (lbf := 4294967295);
rewrite ?unsigned_lit by lia; [ unfold gfile_cells; exact FH | reflexivity | lia | lia | lia | assumption ]. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FH').
rewrite !unsigned_lit in MUc, FH' by lia. clear FH.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.

set (B := bv_unsigned sp + -352) in *.
unfold gfile_cells in FH'.
apply (rw_cells_merge asegs _ _ [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in FH'.
apply (rw_cells_split_CB asegs _ _ [] _ _ _ [1; 31]%nat) in FH'; [|reflexivity].
apply (rw_cells_merge asegs _ _ [_; _; _; _]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 898964); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)]) in FH'.
cbn [app mk_CB_cells cells_size csize Nat.add] in FH'.
match type of FH' with rw_cells _ _ _ (CB 1 ?b1 :: CB 31 ?b31 :: _ :: _ :: CB 96 ?b96 :: _) =>
let v1 := eval vm_compute in b1 in change b1 with v1 in FH'; set (j1 := b31) in FH'; set (j2 := b96) in FH' end.

apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by (subst B; lia).
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).

assert (ISHc : forall mm, munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z m mm -> wmono asegs m mm -> ISH mm).
{ intros mm MUx WMx. eapply ISH_munch_app; [exact ISHm | exact MUx | exact WMx |].
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SNK : SINK_sn Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368) mc []) end.
{ exists jb. split; [|split; [exact FR | split; [reflexivity | split; [unfold zlength, SN_CAP; rewrite LJB; reflexivity | unfold SN_CAP; split; [subst B; lia | split; [lia | split; [subst B; lia | split; [subst B; lia |]]]]]]]].
- unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB. rewrite !Z.add_0_r.
split; [unfold FILE_cells; exact FH'|].
split. { apply (proj2 (rw_cells_app asegs _ _ [CB 0 []] [CB 80 jb])). split; [apply rw_cells_CB0; subst B; lia|]. cbn [cells_size csize Nat.add]. rewrite Z.add_0_r. exact BUFc. }
split; [reflexivity|]. split; [vm_compute; discriminate|]. subst B; lia.
- apply ISHc; assumption. }

assert (PCALL : forall Q ms, implM asegs (printf_model OUT_sn OUTFP_sn fmt args) [] Q ms -> evt asegs (Q r o) ms).
{ intros Q ms H. unfold implM in H. rewrite MODEL in H. exact H. }
pose proof (printf_core_proof (list Z) Fp B 80 _ _ OUT_sn OUTFP_sn
(sn_sink_frame Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_sink_flags Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_topok (bv_unsigned sp + -368))
(sn_out Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))) as PC2.
unfold printf_core_stmt in PC2.
eapply evt_cut.
{ apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_sn, zlength.
all: try (subst B; lia). all: try exact I.
- exact SNK.
- exact BY.
- exact HF.
- reflexivity.
- exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- match goal with H : stk _ _ lo _ |- _ => exact H end.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- exact HSZ. }
cbv beta. intros ms' P. clear PC2 PCALL MODEL AOK HF BY VAA P1 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold INT_MAX in Hr.
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
fix_ret.

destruct SNK3 as (junk3 & WF3 & FR3 & FRL3 & LEN3 & SEPB3 & T13 & T23 & B473 & ISH3).
destruct WF3 as (FC3 & BUF3 & FL3 & LBF3 & B03 & BHI3 & SEPfb3).
pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength, SN_CAP in LEN3.
unfold FILE_cells in FC3. subst j2.
lazymatch type of FC3 with rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; CB 96 _; ?c6] =>
pose proof (rw_cells_unmerge mm Fp [c1; c2; c3; c4]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 898964); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)] [c6]) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
subst j1.
apply (rw_cells_merge asegs _ _ [] [CB 1 _; CB 31 _]) in FC3. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC3.
match type of FC3 with rw_cells _ _ _ (CB 32 ?b :: _) => let v := eval vm_compute in b in change b with v in FC3 end.
lazymatch type of FC3 with rw_cells _ ?mm _ (CB 32 _ :: ?rest) =>
pose proof (rw_cells_unmerge mm Fp [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
lazymatch type of UM with rw_cells _ _ _ (CB 32 ?b :: _) -> _ => let v := eval vm_compute in b in change b with v in UM end.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
zs. zs. zs. brf Kb; [exfalso; lia|].
zs. zs. zs. zs. zs.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] _)) in FC3. destruct FC3 as [F0 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F40 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F48 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F56 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FC3. destruct FC3 as [F64 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FC3. destruct FC3 as [F88 F96]. cbn [cells_size csize Nat.add app] in F96.
replace (Fp + Z.of_nat 40)%Z with (Fp + 40)%Z in F40 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8)%Z with (Fp + 48)%Z in F48 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 56)%Z in F56 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 64)%Z in F64 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24)%Z with (Fp + 88)%Z in F88 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8)%Z with (Fp + 96)%Z in F96 by lia.
unfold snfile_rest in FR3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR3. destruct FR3 as [F148 FR3]. cbn [cells_size csize Nat.add app] in FR3.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR3. destruct FR3 as [F152 F160]. cbn [cells_size csize Nat.add app] in F160.
replace (Fp + 148 + Z.of_nat 4)%Z with (Fp + 152)%Z in F152 by lia.
replace (Fp + 148 + Z.of_nat 4 + Z.of_nat 8)%Z with (Fp + 160)%Z in F160 by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ BUF3) as SRC3. cbn [cells_bytes cbytes app] in SRC3. rewrite app_nil_r in SRC3.
apply bytes_at_app in SRC3. destruct SRC3 as [SRC3 _].
replace (Z_to_bv 64 (B + Z.of_nat (length o))) with (Z_to_bv 64 (B + zlength o)) in F40 by reflexivity.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD3 : (0 < zlength o)%Z -> rng_ok mc D (zlength o))
end.
{ intros K. eapply rng_ok_munch; [exact (RD K) | exact MU | exact WM |].
pose proof (proj1 (proj2 (RD K))) as D47. unfold zlength in *.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
eapply evt_cut.
{ eapply sn_write_spec with (o := o) (B := B) (n := n) (D := D) (CK := CK) (dn := dn) (bufp := B) (Fp := Fp) (junk := junkd) (lo := lo);
rewrite ?unsigned_lit by lia; unfold zlength, SN_WRITE_STACK, MEMCPY_ICPT_STACK;
[ reflexivity | reflexivity | exact F40 | exact F56 | exact F88 | exact F152 | | exact SRC3 | | exact ROOM | lia | subst B; lia | subst B; lia
| match goal with H : stk _ _ lo _ |- _ => exact H end | exact GLO | lia | assumption
| subst B; lia | lia | lia | lia | lia | lia | subst B; lia | lia | subst B; lia | subst B; lia
| exact (proj2 (proj2 ISH3)) | exact (proj1 (proj2 ISH3))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH3)); [unfold szone; right; left; subst B; lia | lia]
| exact RD3 ].
all: lazymatch goal with |- rw_cells _ _ ?a _ => match goal with H : rw_cells _ _ a _ |- _ => exact H end end. }
cbv beta. intros ms' P.
unfold sn_write_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4 & CK4 & DST4 & F40' & F56' & SRC4).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
fix_ret.

zs. zs. zs. zs. zs.
zs. replace (0 <? B)%Z with true by (symmetry; apply Z.ltb_lt; subst B; lia). cbn [Z.b2z].
zs. zs. rewrite ?Z.lor_0_l. zs.
zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. zs. zs. zs. zs. rewrite ?Z.lor_0_l. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6575456 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.
try rewrite (land_M64_id r) by lia.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z [C8 apv] |- _ => rename H into APC4 end.
match goal with H : rw_cells _ ?mm B _ |- _ => rename H into BUF4 end.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => rename H into ST5 end.
release_frame APC4 ST5 (bv_unsigned sp + -360)%Z.
release_frame AP2 ST5 B.
release_frame BUF4 ST5 (bv_unsigned sp + -272)%Z.
release_frame FRv ST5 (bv_unsigned sp).
lazymatch goal with F0 : rw_cells _ ?mm Fp _, F40 : rw_cells _ ?mm (Fp + 40)%Z _, F48 : rw_cells _ ?mm (Fp + 48)%Z _, F56 : rw_cells _ ?mm (Fp + 56)%Z _,
F64 : rw_cells _ ?mm (Fp + 64)%Z _, F88 : rw_cells _ ?mm (Fp + 88)%Z _, F96 : rw_cells _ ?mm (Fp + 96)%Z _,
F148 : rw_cells _ ?mm (Fp + 148)%Z _, F152 : rw_cells _ ?mm (Fp + 152)%Z _, F160 : rw_cells _ ?mm (Fp + 160)%Z _ |- _ =>
assert (FALL : rw_cells asegs mm Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 898964); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 bufp)]
++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode'; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)]
++ [C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 CK)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F0|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F40|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F48|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F56|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F64|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F88|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F96|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F148|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [piece F152|];
piece F160
| ] end.
destruct (rw_cells_forget _ _ _ _ FALL) as [fjunk FJ]. cbn [cells_size csize Nat.add app] in FJ.
apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
split; [exact ST5|].
split; [split; [exact SSP1 | exact SSP2]|].
split; [exact DST4|]. split; [exact CK4|]. exact FJ.
Qed.
