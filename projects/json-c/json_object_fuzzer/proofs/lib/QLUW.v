(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKY2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXDj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXDj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q45h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q45h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q25t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q25t. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7DP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7DP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHqi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHqi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi08.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjgW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV3O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6w1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWwJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWwJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4I1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4I1.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac inl := first [solve [cbn; repeat first [left; reflexivity | right]; reflexivity] | cbn; tauto].
Import QWRO(aentry, mkAE, ae_sp0, ae_stack_top, ae_fs_base, ae_L, ae_stack_bottom)
QFQR(rlay, mkRL, rl_T, rl_ctx, rl_dn, rl_ssb, rl_dtls, prim_lo, region_info, ptrarr_lo, A_TP, A_INSTANCE, A_TLS_TSD, A_TSD_MAIN)
QKBN(RTconst, rt_img_cells, rt_rw_cells, rt_T_cells).

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Local Lemma band0_range : 0x7fff7f800000 <= 0x7fff7f800000 <= 0x7fffff800000.
Proof. lia. Qed.
Local Definition band0 : Band := mkBand 0x7fff7f800000 band0_range (wz 0).
Definition RE0 : aentry := mkAE 0 0 0 (Q6sh.mkALay 0 0 []).
Definition X0 : rlay := mkRL 0 0 0 0 0.

Definition RT_L1 : list (Z * list cell) := Eval vm_compute in firstn 24 (@rt_img_cells band0 RE0 X0).
Definition RT_L2 : list (Z * list cell) := Eval vm_compute in firstn 3 (skipn 26 (@rt_img_cells band0 RE0 X0)).
Definition RT_L3 : list (Z * list cell) := Eval vm_compute in firstn 11 (skipn 32 (@rt_img_cells band0 RE0 X0)).
Definition RT_L4 : list (Z * list cell) := Eval vm_compute in firstn 7 (skipn 44 (@rt_img_cells band0 RE0 X0)).
Definition RT_L5 : list (Z * list cell) := Eval vm_compute in skipn 52 (@rt_img_cells band0 RE0 X0).

Lemma rt_img_cells_split {BAND : Band} : forall RE X,
rt_img_cells RE X =
RT_L1 ++ [ (A_INSTANCE + 32, [C8 (wz (Q6sh.al_space_beg (ae_L RE))); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz (region_info RE)); C1 (b8 0)]);
(A_INSTANCE + 64, [C8 (wz 0x1000); C8 (wz (ptrarr_lo RE))]) ]
++ RT_L2 ++ [ (A_TSD_MAIN, [C8 (wz (rl_ctx X))]); (A_TP, [C8 (wz (ae_fs_base RE))]); (A_TP + 0x8, [C8 (wz (rl_dtls X))]) ]
++ RT_L3 ++ [ (A_INSTANCE + 80, [C8 (wz (ptrarr_lo RE)); C8 (wz 0x800000); C8 (wz 0x1a475)]) ]
++ RT_L4 ++ [ (0x645560, [C8 band_guard]) ] ++ RT_L5.
Proof. intros RE X. reflexivity. Qed.

Definition E_SB : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 65536).
Definition E_RI : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 137439019008).
Definition E_PG (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).
Definition E_ST : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10)).
Definition E_SBOT : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) (ELit (-8388608)).

Definition RT_SYM_FACTS : list kentry :=
[ KWord (SA (ELit 0) 977784) 8 E_SB; KWord (SA (ELit 0) 977800) 8 E_RI;
KWord (SA (ELit 0) 977824) 8 (E_PG 236); KWord (SA (ELit 0) 977832) 8 (E_PG 236);
KWord (SA (ELit 0) 6580544) 8 (E_PG 238); KWord (SA (ELit 0) 6444320) 8 (E_PG 406); KWord (SA (ELit 0) 6444328) 8 (E_PG 330);
KWord (SA (ELit 0) 6575456) 8 (EVar 45);

KWord (SA (E_PG 237) 0) 8 (E_PG 238); KWord (SA (E_PG 237) 8) 8 E_ST; KWord (SA (E_PG 237) 16) 8 E_SBOT;
KWord (SA (E_PG 237) 24) 8 (ELit 0); KWord (SA (E_PG 237) 32) 8 (ELit 0); KWord (SA (E_PG 237) 40) 1 (ELit 0);
KZero (SA (E_PG 237) 41) (ELit 7);
KWord (SA (E_PG 237) 48) 8 (ELit 0x625c58); KWord (SA (E_PG 237) 56) 8 (ELit 0x625d40); KWord (SA (E_PG 237) 64) 8 (ELit 0x625528);
KWord (SA (E_PG 237) 72) 8 (E_PG 406);

KWord (SA (E_PG 238) 8) 4 (ELit 0); KWord (SA (E_PG 238) 152) 8 (E_PG 237);

KWord (SA (E_PG 330) 24) 8 (ELit 6444320);

KRange (EVar 237) 1 34359736319; KRange (EVar 238) 1 34359736304; KRange (EVar 330) 1 34359736319;
KRange (EVar 406) 1 34359733495; KRange (EVar 236) 1 34359734272; KRange (EVar 208) 4295491576 34326181871;
KRange (EVar 209) 0 15; KRange (EVar 0) 4294901760 4294967295; KRange (EVar 10) 0 8 ].

Definition kspanR (K : kentry) : option (Z * Z) :=
match K with
| KWord sa w _ => Some (a_off sa, a_off sa + Z.of_nat w)
| KZero sa (ELit n) | KFill sa (ELit n) _ => Some (a_off sa, a_off sa + n)
| KImg lo hi => Some (lo, hi)
| _ => None
end.
Definition kwinR (k : list kentry) (lo hi : Z) : list kentry :=
List.filter (fun K => match kspanR K with Some (l, h) => (l <? hi) && (lo <? h) | None => false end) k.
Lemma know_ok_winR : forall E m k lo hi, know_ok asegs E m k -> know_ok asegs E m (kwinR k lo hi).
Proof.
intros E m k lo hi KO. unfold know_ok, kwinR in *. apply Forall_forall. intros K HK. apply List.filter_In in HK as [HK _].
exact (proj1 (Forall_forall _ _) KO K HK).
Qed.
Definition kn_cellsR (k : list kentry) (a : Z) (cs : list cell) : bool := kn_cells (kwinR k a (a + Z.of_nat (cells_size cs))) a cs.
Definition kn_rw_cellsR (k : list kentry) (a : Z) (cs : list cell) : bool := kn_rw_cells (kwinR k a (a + Z.of_nat (cells_size cs))) a cs.
Lemma kn_cellsR_sound : forall E m kn, know_ok asegs E m kn -> forall a cs, kn_cellsR kn a cs = true -> ro_cells asegs m a cs.
Proof. intros E m kn KO a cs H. exact (kn_cells_sound E m _ (know_ok_winR E m kn _ _ KO) a cs H). Qed.
Lemma kn_rw_cellsR_sound : forall E m kn a cs, know_ok asegs E m kn -> kn_rw_cellsR kn a cs = true -> rw_cells asegs m a cs.
Proof. intros E m kn a cs KO H. exact (kn_rw_cells_sound E m _ a cs (know_ok_winR E m kn _ _ KO) H). Qed.

Definition rt_checks (k : list kentry) : bool :=
forallb (fun ac => kn_cellsR k (fst ac) (snd ac)) (RT_L1 ++ RT_L2 ++ RT_L3 ++ RT_L4 ++ RT_L5)
&& forallb (fun ac => kn_rw_cellsR k (fst ac) (snd ac)) rt_rw_cells
&& kn_cellsR k (A_INSTANCE + 40) [C4 (wz 0xffffffff); C4 (wz 0)] && kn_cellsR k (A_INSTANCE + 56) [C1 (b8 0)]
&& kn_cellsR k (A_INSTANCE + 64) [C8 (wz 0x1000)] && kn_cellsR k (A_INSTANCE + 88) [C8 (wz 0x800000); C8 (wz 0x1a475)]
&& kn_has_all RT_SYM_FACTS k.

Lemma RT_CHECKS : forall w ch, HSCLASS_S w ch -> rt_checks (kn_view ch) = true.  Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Lemma ro_cells_cons1 : forall m A c cs,
ro_cells asegs m A [c] -> ro_cells asegs m (A + Z.of_nat (csize c)) cs -> ro_cells asegs m A (c :: cs).
Proof.
intros m A c cs H1 H2. apply (proj2 (ro_cells_app asegs m A [c] cs)). split; [exact H1|].
cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma Forall_cells_of_checks : forall E m kn l, know_ok asegs E m kn ->
forallb (fun ac => kn_cellsR kn (fst ac) (snd ac)) l = true ->
Forall (fun ac => ro_cells asegs m (fst ac) (snd ac)) l.
Proof.
intros E m kn l KO H. rewrite forallb_forall in H. apply Forall_forall. intros ac Hin.
exact (kn_cellsR_sound E m kn KO (fst ac) (snd ac) (H ac Hin)).
Qed.

Lemma kn_word8_den : forall E m kn a v, know_ok asegs E m kn -> kn_has (KWord (SA (ELit 0) a) 8 v) kn = true ->
0 <= a -> a + 8 <= 2^64 -> ro_cells asegs m a [C8 (edenot E v)].
Proof.
intros E m kn a v KO HK Ha Hb.
pose proof (proj1 (List.Forall_forall _ _) KO _ (kn_has_In _ _ HK)) as OK. cbn [kentry_ok] in OK. destruct OK as (W8 & FL & RD).
assert (ES : estart E (SA (ELit 0) a) = a) by (apply lit0_estart; reflexivity).
pose proof (flat_u E _ _ FL) as AU. rewrite ES in AU.
assert (WA : adenot E (SA (ELit 0) a) = wz a).
{ apply bv_eq. rewrite AU. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. change (bv_modulus 64) with (2^64). lia. }
rewrite WA in RD.
pose proof (rdn_bytes_at asegs m 8 a _ ltac:(lia) ltac:(lia) RD) as BA.
split; [inl|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact BA.
Qed.

Section RT.
Context {BAND : Band}.
Variables (sp : word) (w : bool) (E : env) (m : word -> option byte) (kn : list kentry).
Hypothesis KO : know_ok asegs E m kn.
Hypothesis CK : rt_checks kn = true.
Hypothesis HG : band_guard = guard_main E.

Lemma sym_fact : forall K, In K RT_SYM_FACTS -> kn_has K kn = true.
Proof.
intros K HK. unfold rt_checks in CK. apply andb_prop in CK as [_ H]. unfold kn_has_all in H. rewrite forallb_forall in H. exact (H K HK).
Qed.
Lemma sym_fact' : forall K, kn_has K RT_SYM_FACTS = true -> kn_has K kn = true.
Proof. intros K HK. apply sym_fact. apply kn_has_In. exact HK. Qed.

Ltac rng v lo hi := let H := fresh "B" in
pose proof (kn_range_var E m kn KO v lo hi (sym_fact' (KRange (EVar v) lo hi) ltac:(vm_compute; reflexivity))) as H.

Ltac kw K zb zv H :=
pose proof (kn_word E m kn _ _ _ _ zb zv KO (sym_fact' K ltac:(vm_compute; reflexivity)) eq_refl ltac:(lia) eq_refl ltac:(inl)) as H;
cbn [wcell] in H.

Theorem RTconst_main_of_kn : RTconst (RE_main sp w E) (X_main E) m.
Proof.
pose proof CK as CK'. unfold rt_checks in CK'.
apply andb_prop in CK' as [CK' _]. apply andb_prop in CK' as [CK' C88]. apply andb_prop in CK' as [CK' C64].
apply andb_prop in CK' as [CK' C56]. apply andb_prop in CK' as [CK' C40]. apply andb_prop in CK' as [CL CRW].
rewrite !forallb_app in CL. apply andb_prop in CL as [CL1 CL]. apply andb_prop in CL as [CL2 CL]. apply andb_prop in CL as [CL3 CL].
apply andb_prop in CL as [CL4 CL5].
rng 237%nat 1 34359736319. rng 238%nat 1 34359736304. rng 330%nat 1 34359736319.
rng 406%nat 1 34359733495. rng 236%nat 1 34359734272. rng 208%nat 4295491576 34326181871.
rng 209%nat 0 15. rng 0%nat 4294901760 4294967295. rng 10%nat 0 8.
unfold RTconst. split; [| split; [| split; [| split; [| split]]]].
-
rewrite rt_img_cells_split.
repeat (apply Forall_app; split); try (eapply Forall_cells_of_checks; [exact KO| assumption]).
+
constructor; [| constructor; [| constructor]]; cbn [fst snd].
* kw (KWord (SA (ELit 0) 977784) 8 E_SB) 0 (4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209) + 65536) K1.
kw (KWord (SA (ELit 0) 977800) 8 E_RI) 0 (4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209) + 137439019008) K2.
change (Q6sh.al_space_beg (ae_L (RE_main sp w E))) with (SB E). change (region_info (RE_main sp w E)) with (SB E + 2^37).
replace (SB E) with (4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209) + 65536) by (unfold SB, PRES; lia).
replace (4096 * bv_unsigned (ev E 208) + -4096 * bv_unsigned (ev E 209) + 65536 + 2 ^ 37) with (4096 * bv_unsigned (ev E 208) + (-4096) * bv_unsigned (ev E 209) + 137439019008) by lia.
apply ro_cells_cons1; [exact K1|]. cbn [csize].
apply (proj2 (ro_cells_app asegs m _ [C4 (wz 4294967295); C4 (wz 0)] _)). split; [exact (kn_cellsR_sound E m kn KO _ _ C40)|]. cbn [cells_size csize Nat.add].
apply ro_cells_cons1; [exact K2|]. cbn [csize]. exact (kn_cellsR_sound E m kn KO _ _ C56).
* kw (KWord (SA (ELit 0) 977824) 8 (E_PG 236)) 0 (4096 * bv_unsigned (ev E 236)) K3.
change (ptrarr_lo (RE_main sp w E)) with (4096 * bv_unsigned (ev E 236)).
apply (proj2 (ro_cells_app asegs m _ [C8 (wz 4096)] _)). split; [exact (kn_cellsR_sound E m kn KO _ _ C64)| exact K3].
+
kw (KWord (SA (ELit 0) 6580544) 8 (E_PG 238)) 0 (4096 * bv_unsigned (ev E 238)) K4.
kw (KWord (SA (ELit 0) 6444320) 8 (E_PG 406)) 0 (4096 * bv_unsigned (ev E 406)) K5.
kw (KWord (SA (ELit 0) 6444328) 8 (E_PG 330)) 0 (4096 * bv_unsigned (ev E 330)) K6.
constructor; [exact K4|]. constructor; [exact K5|]. constructor; [exact K6|]. constructor.
+
kw (KWord (SA (ELit 0) 977832) 8 (E_PG 236)) 0 (4096 * bv_unsigned (ev E 236)) K7.
constructor; [| constructor]. cbn [fst snd]. change (ptrarr_lo (RE_main sp w E)) with (4096 * bv_unsigned (ev E 236)).
apply ro_cells_cons1; [exact K7|]. exact (kn_cellsR_sound E m kn KO _ _ C88).
+
constructor; [| constructor]. cbn [fst snd]. rewrite HG. unfold guard_main.
exact (kn_word8_den E m kn 6575456 (EVar 45) KO (sym_fact' (KWord (SA (ELit 0) 6575456) 8 (EVar 45)) ltac:(vm_compute; reflexivity)) ltac:(lia) ltac:(lia)).
-
change (rl_T (X_main E)) with (4096 * bv_unsigned (ev E 237)). unfold rt_T_cells.
change (rl_ctx (X_main E)) with (4096 * bv_unsigned (ev E 238)). change (ae_stack_top (RE_main sp w E)) with (st_main E).
change (ae_fs_base (RE_main sp w E)) with (4096 * bv_unsigned (ev E 406)). unfold ae_stack_bottom. change (ae_stack_top (RE_main sp w E)) with (st_main E). unfold st_main.
kw (KWord (SA (E_PG 237) 0) 8 (E_PG 238)) (4096 * bv_unsigned (ev E 237)) (4096 * bv_unsigned (ev E 238)) T0.
kw (KWord (SA (E_PG 237) 8) 8 E_ST) (4096 * bv_unsigned (ev E 237)) (32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10)) T1.
kw (KWord (SA (E_PG 237) 16) 8 E_SBOT) (4096 * bv_unsigned (ev E 237)) (32768 * bv_unsigned (ev E 0) + 4096 * bv_unsigned (ev E 10) - 8388608) T2.
kw (KWord (SA (E_PG 237) 24) 8 (ELit 0)) (4096 * bv_unsigned (ev E 237)) 0 T3.
kw (KWord (SA (E_PG 237) 32) 8 (ELit 0)) (4096 * bv_unsigned (ev E 237)) 0 T4.
kw (KWord (SA (E_PG 237) 40) 1 (ELit 0)) (4096 * bv_unsigned (ev E 237)) 0 T5.
pose proof (kn_zero_ro E m kn KO _ 41 7 (4096 * bv_unsigned (ev E 237)) (sym_fact' (KZero (SA (E_PG 237) 41) (ELit 7)) ltac:(vm_compute; reflexivity))
eq_refl ltac:(lia) ltac:(lia) (4096 * bv_unsigned (ev E 237) + 41) [CB 7 (repeat (b8 0) 7)] eq_refl ltac:(lia) ltac:(cbn; lia)) as T6.
kw (KWord (SA (E_PG 237) 48) 8 (ELit 0x625c58)) (4096 * bv_unsigned (ev E 237)) 0x625c58 T7.
kw (KWord (SA (E_PG 237) 56) 8 (ELit 0x625d40)) (4096 * bv_unsigned (ev E 237)) 0x625d40 T8.
kw (KWord (SA (E_PG 237) 64) 8 (ELit 0x625528)) (4096 * bv_unsigned (ev E 237)) 0x625528 T9.
kw (KWord (SA (E_PG 237) 72) 8 (E_PG 406)) (4096 * bv_unsigned (ev E 237)) (4096 * bv_unsigned (ev E 406)) T10.
rewrite Z.add_0_r in T0.
repeat (apply ro_cells_cons1; [assumption| cbn [csize]; rewrite <- ?Z.add_assoc; cbn [Z.add Pos.add Pos.succ Z.of_nat Pos.of_succ_nat]]).
constructor; [exact I|]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
- kw (KWord (SA (E_PG 238) 8) 4 (ELit 0)) (4096 * bv_unsigned (ev E 238)) 0 KC1. exact KC1.
- kw (KWord (SA (E_PG 238) 152) 8 (E_PG 237)) (4096 * bv_unsigned (ev E 238)) (4096 * bv_unsigned (ev E 237)) KC2. exact KC2.
- kw (KWord (SA (E_PG 330) 24) 8 (ELit 6444320)) (4096 * bv_unsigned (ev E 330)) 6444320 KC3. exact KC3.
- rewrite forallb_forall in CRW. apply Forall_forall. intros ac Hin. exact (kn_rw_cellsR_sound E m kn (fst ac) (snd ac) KO (CRW ac Hin)).
Qed.
End RT.

Theorem RTconst_at_main : at_main_stmt (fun BAND sp w E m => @RTconst BAND (RE_main sp w E) (X_main E) m).
Proof.
intros sp rdraw brk0 argv envp fs uid hw E R FULL mo Hsp Hva Hve Hfit w ch HCL CS BAND HB HG.
apply (RTconst_main_of_kn sp w E _ (kn_view ch)); [| exact (RT_CHECKS w ch HCL) | exact HG].
exact (main_know_view sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS).
Qed.
