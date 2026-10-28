(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qn1e QO3A Q7m0 QSpR QuJV QCPB QBxa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Udbv UFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qn1e QRjH.Mq0 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QBxa.Mq2 QBxa.Mq6 QSpR.Mq3.
Import UFeQ Udbv UFOH.Mq0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma D_main_none {AMB : Amb} : forall sp0 av ev tid (i : Z),
valid_argv av -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
D_main_missb i 1 = true ->
D_main sp0 av ev tid (Z_to_bv 64 i) = None.
Proof.
intros sp0 av ev tid i Hva Hlo Hhi Hb.
pose proof (u64_range tid) as Ht.
unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
end.
repeat match goal with
| H : range_disjoint_b _ _ _ = true |- _ =>
apply range_disjoint_djw in H; cbn [fst snd] in H
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : true = true |- _ => clear H
end.
assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
repeat (rewrite QBxa.Mq2.wbytes_outside;
[ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
| rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
reflexivity.
Qed.

#[using="Type"] Lemma seg_rom_high : forall (a : word), (0x99000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
intros a Ha. unfold seg_rom. unfold memory_read.
cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
cbn [Z.of_N].
repeat (lazymatch goal with
| |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
end).
reflexivity.
Qed.

#[using="Type"] Lemma rdn_pointwise_inv : forall segs m n (a : word) bs,
(forall j, (j < n)%nat -> seg_rom segs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
rdn segs m a n = Some bs ->
forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
intros segs m n. induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
destruct (m a) as [b|] eqn:Hm.
- destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
destruct j as [|j].
+ rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
+ cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
apply Hseg. lia.
- rewrite H0 in Hr. discriminate.
Qed.

Section MainEntry.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable ev : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev tid regs mem.

Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

Definition p0 : word := cat_argv_ptr sp0 av ev 0.
Definition p1 : word := cat_argv_ptr sp0 av ev 1.
Definition auxvp : word := auxv_w sp0 av ev.
Definition rnd : word := at_random_ptr sp0 av ev.

Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs ++ [ssp_canary].
Definition blobs0 : list (list byte) := [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; rnd_bytes].
Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr_main : list expr :=
[ELit 0; ELit 0x508ac; spx (-48); ELit 0x10800; ELit 0x77c00; EVar 11; EVar 12; EVar 13;
spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
EVar 22; EVar 23; ELit 0x20b84; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_stack : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
KWr (SA (EVar 0) (-8388608)) 8388608;
KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

Definition kn_auxv : list kentry :=
[KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
KAlign (EVar 3) 8; KAlign (EVar 4) 8;
KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 11);
KWord (SA (EVar 3) 48) 8 (ELit 16);
KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
KWord (SA (EVar 3) 80) 8 (ELit 11);
KWord (SA (EVar 3) 96) 8 (ELit 12);
KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0);
KBlob (SA (EVar 4) 0) (ELit 16) 2 ].

Definition kn_image : list kentry :=
[KWr (SA (ELit 0) 0x66000) 0x33000;
KImg 0x10000 0x66f30;
KImg 0x66f31 0x77b30; KImg 0x97c08 0x97c18;
KWord (SA (ELit 0) 0x77b38) 8 (ELit 0x77b38);
KWord (SA (ELit 0) 0x77b58) 4 (EVar 5);
KImg 0x77b5c 0x77b60;
KImg 0x77b64 0x77bb0; KImg 0x77bb8 0x77bd0; KImg 0x77bd8 0x77bf0;
KWord (SA (ELit 0) 0x77bf0) 8 (EVar 38);
KImg 0x77c00 0x77c10; KImg 0x77c20 0x97c08; KImg 0x97c40 0x97e70;
KWord (SA (ELit 0) 0x97e70) 8 (EVar 38);
KImg 0x97e78 0x97e80;
KImg 0x97e91 0x97e98; KWord (SA (ELit 0) 0x97e98) 8 (EVar 3);
KWord (SA (ELit 0) 0x97ec0) 8 (ELit 4096);
KImg 0x97ec8 0x97ef8;  KImg 0x97f00 0x99000;
KRange (EVar 5) 1 4194303;
KImg 0 0x1000 ].

Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

#[using="Type"] Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
intros n Hn.
destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

#[using="Type"] Lemma regs_ok_by_index : forall E sr R,
(forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
regs_ok E sr R.
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
reflexivity.
- pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section MainEntryProofs.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv tid regs mem.

Local Notation E := (E0 sp0 a0s path envv tid regs).

#[using="Type"] Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] ++ junk_vals regs ++ [ssp_canary]) (Z_to_bv 64 0).
Proof. intros n. reflexivity. Qed.

#[using="Type"] Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
rewrite app_nth2_plus. rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; exact Hi).
unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.
End FPGEN1.

Section MainRegs.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv tid regs mem.
Local Notation E := (E0 sp0 a0s path envv tid regs).

Ltac reg_case :=
cbn [nth sr_main all_regs];
first [ rewrite (spx_val sp0 a0s path envv tid regs)
| lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot E (EVar n)) with (ev E n);
first [ rewrite (ev_junk sp0 a0s path envv tid regs (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
| exact (me_s2 _ _ _ _ _ _ ME)
| rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
| rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
| rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
| rewrite (me_a2 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
| rewrite (me_s3 _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
| rewrite (me_s1 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
| rewrite (me_a0 _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
| apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
| idtac ].

#[using="mem av Hvsp Htid ME"] Theorem main_regs_ok : regs_ok E sr_main regs.
Proof.
pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
Qed.
End MainRegs.

Section KnowProofs.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Let av := [a0s; path].
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv tid regs mem.
Local Notation E := (E0 sp0 a0s path envv tid regs).

#[using="Hvsp"] Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
#[using="Hvsp"] Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
#[using="Hvsp"] Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
#[using="Type"] Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke1 : ev E 1 = p0 sp0 a0s path envv. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke2 : ev E 2 = p1 sp0 a0s path envv. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke4 : ev E 4 = rnd sp0 a0s path envv. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
#[using="Type"] Lemma ke38 : ev E 38 = ssp_canary. Proof. reflexivity. Qed.

#[using="av Hva Hve Hvsp ME"] Lemma know_stack : know_ok RSEGS E mem kn_stack.
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
unfold kn_stack, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
- split; [lia | exact Hal].
- lia.
- split; [lia|]. intros d m Hd Hm.
apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
pose proof (read_argc_w RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva) as Hr. unfold wmem in Hr.
rewrite (Hr Hve) by (unfold sp_window_hi; lia).
rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_null RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv a_uid) in Hr by (try rewrite u_small by lia; lia).
unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
Qed.

#[using="Type"] Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
Proof. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

#[using="AMB Hva Hve Hvsp"] Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
/\ (Z.of_nat (auxv_off av envv) + 160 <= 2240000)%Z.
Proof.
pose proof kp_lo. pose proof kp_hi.
pose proof (auxv_off_bound RPH sp0 av envv a_uid a_hwcap a_rnd) as Hb.
pose proof (lay_bsb_len RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve) as Hl.
rewrite auxvp_eq. rewrite u_small by lia. lia.
Qed.

#[using="Hva Hve Hvsp"] Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
/\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
/\ (bv_unsigned (rnd sp0 a0s path envv) mod 8 = 0)%Z
/\ (forall j n, (j + n <= 16)%nat ->
rdn RSEGS (stack_to_mem sp0 (entry_stack_image RPH sp0 av envv a_uid a_hwcap a_rnd))
(Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat j)) n = Some (firstn n (skipn j rnd_bytes))).
Proof.
pose proof kp_lo as HLO. pose proof kp_hi as HHI.
pose proof (lay_bsb_len RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve) as Hl.
destruct (rnd_facts RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
as (A & B & C & D & F).
unfold rnd, rnd_bytes. subst av. repeat split; try assumption; try lia.
Qed.

#[using="tid regs av Hva Hve Hvsp ME"] Lemma auxv_word_at : forall j, (j < 20)%nat ->
rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
= Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rnd sp0 a0s path envv) a_uid a_hwcap) (Z_to_bv 64 0))).
Proof.
intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
destruct auxvp_u as [Hu Hb].
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia).
replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
rewrite (read_auxv_word RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
rewrite n_to_le_8_spec. unfold rnd. reflexivity.
Qed.

Ltac kw_auxv j :=
split; [lia|]; split; [lia|];
unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
replace k with (8 * Z.of_nat j)%Z by reflexivity end;
rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

#[using="av Hva Hve Hvsp ME"] Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
unfold kn_auxv, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
try rewrite Hau; try lia.
-  split; [lia|].
destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
by (unfold auxv_off; subst av; cbn [length]; lia).
apply Z_mod_mult.
- kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
- kw_auxv 6%nat. - kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat.
- kw_auxv 12%nat. - kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat.
- kw_auxv 18%nat. - kw_auxv 19%nat.
-
rewrite u_small by lia. split; [lia|]. split; [reflexivity|]. intros i Hi.
assert (Hr : rdn RSEGS mem (rnd sp0 a0s path envv) 16 = Some rnd_bytes).
{ rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd) as Hw. unfold wmem in Hw.
rewrite Hw by lia.
pose proof (Hr4 0%nat 16%nat ltac:(lia)) as H16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H16. exact H16. }
pose proof (rdn_pointwise_inv RSEGS mem 16 (rnd sp0 a0s path envv) _
ltac:(intros j Hj; apply seg_rom_high; rewrite u_small by lia; lia)
ltac:(lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
rewrite Z2Nat.id in Hp by lia.
replace (bv_unsigned (rnd sp0 a0s path envv) + 0 + i)%Z with (bv_unsigned (rnd sp0 a0s path envv) + i)%Z by lia.
exact Hp.
Qed.

#[using="Hvsp"] Lemma D_main_auxvp : forall segs,
rdn segs (D_main sp0 av envv tid) (Z_to_bv 64 0x97e98) 8
= Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
Proof.
intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

#[using="Type"] Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0x66000) 0x33000 = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
(lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
Proof.
intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

#[using="Type"] Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
(lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
Proof.
intros lo n i H Hlo Hhi. unfold D_main_missb in *.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
apply (proj1 (forallb_forall _ _) H1). exact Hc.
Qed.

#[using="av Hva Hvsp ME"] Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x99000)%Z ->
kentry_ok RSEGS E mem (KImg lo hi).
Proof.
intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
assert (Hlo0 : (0 <= lo)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
apply Z.leb_le in Hb. exact Hb. }
cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 av envv tid i Hva); [lia | lia |].
apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.

Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

Ltac kw_pre :=
split; [lia|]; split; [lia|];
unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
Ltac kw_data L :=
kw_pre;
rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
rewrite (L RSEGS); try reflexivity.
Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

#[using="av Hva Hvsp Htid ME"] Lemma know_image : know_ok RSEGS E mem kn_image.
Proof.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
unfold kn_image, know_ok.
repeat apply Forall_cons; try apply Forall_nil;
try kimg;
cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke38; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
rewrite ?(u_small 0) by lia; cbn [Z.add].
-  split; [lia|]. intros d m Hd Hm.
eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x66000) (Z_to_bv 64 (0x66000 + d)) 0x33000 m 0x66000 0x99000);
[reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- kw_data (D_main_self sp0 av envv tid).
- kw_mem (main_entry_tid sp0 av envv tid Hlo regs mem ME).
- kw_data (D_main_canary sp0 av envv tid).
- kw_mem (main_entry_guard sp0 av envv tid Hlo regs mem ME).
- kw_data D_main_auxvp.
- kw_data (D_main_pagesize sp0 av envv tid Hva).
-  lia.
Qed.

#[using="av Hva Hve Hvsp Htid ME"] Theorem main_know_ok : know_ok RSEGS E mem kn_main.
Proof.
unfold kn_main, know_ok.
apply Forall_app; split; [apply know_stack|].
apply Forall_app; split; [apply know_auxv | apply know_image].
Qed.

#[using="AMB tid regs Hva Hve Hvsp ME"] Lemma main_str : forall k, (k < 2)%nat ->
rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
/\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
/\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
/\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
pose proof (lay_bsb_nw RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (struct_av_bound av envv Hva Hve) as Hsb.
pose proof (total_arg_bytes_firstn_le k av) as Hf.
pose proof (argv_str_len av Hva k Hk') as Hlen.
repeat split.
- rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd) as Hw. unfold wmem in Hw. rewrite Hw by lia.
apply read_argv_cstr_k; [exact Hk' | exact Hnw].
- exact B1.
- lia.
- exact Hlen.
Qed.
End KnowProofs.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMOs.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFOH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZSc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZSc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UsN4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UsN4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlKb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlKb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U39n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U39n.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma rz_emit_nil : forall c K, realizes RSEGS c K -> realizes RSEGS c (t_emit [] K).
Proof.
intros c K H. eapply rz_conseq; [exact H|].
apply t_eq_sym. apply t_emit_nil_eq. exact (realizes_nonempty _ _ _ H).
Qed.

#[using="Type"] Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
(k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

#[using="Type"] Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
(length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

#[using="Type"] Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
\/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
intros b k Hk Hle. unfold at_. pose proof (u64_range b).
destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
- right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
- left. u_norm. reflexivity.
Qed.

Section Loop.
Variables (su f fd : Z) (l bufp bufsz can ret : word).
Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
Variable mem1 : word -> option byte.
Variable model : Model.
Variable K : TSet.

Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
Hypothesis SUhi : (su <= 0x800000000000)%Z.
Hypothesis Flo : (0x66000 <= f)%Z.
Hypothesis Fhi : (f + 232 <= 0x97e70)%Z.
Hypothesis FD : (0 < fd < 2147483648)%Z.
Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hret : ret_ok ret.
Hypothesis HKnil : K [].
Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x97e70) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

Definition LM (m : word -> option byte) : Prop :=
(forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

Hypothesis HK : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = e8 -> getr regs' 9 = e9 ->
getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
LM m ->
realizes RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.

Definition RI (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
/\ getr regs 21 = Z_to_bv 64 0x97e70 /\ getr regs 3 = g3 /\ getr regs 4 = g4
/\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
/\ getr regs 26 = g26 /\ getr regs 27 = g27.

#[using="Type"] Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
Proof.
intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
(P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
Qed.

#[using="Type"] Lemma LM_refl : LM mem1.
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

#[using="Type"] Lemma LM_rdn : forall m (a : word) n bs,
LM m -> rdn RSEGS mem1 a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
rdn RSEGS m a n = Some bs.
Proof.
intros m a n bs [E G] H Hnw D.
rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
intros x Hx. apply E. lia.
Qed.

#[using="Type"] Lemma LM_store_ok : forall m (a : word) n,
LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

#[using="SUlo SUhi"] Lemma LM_wbytes8 : forall m (a : Z) (v : word),
LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
Proof.
intros m a v [E G] Hlo Hhi. split.
- intros x Hx. rewrite wbytes_outside.
+ apply E, Hx.
+ unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.

#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish : forall regs m,
RI regs -> LM m ->
realizes RSEGS (mkCfg (mkst regs (0x55270 : word) m (seg_rom RSEGS)) model) K.
Proof.
intros regs m RIr LMm.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
try assumption.
all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
apply HK; try assumption.
- rewrite Q23; exact R23.
- rewrite Q24; exact R24.
- rewrite Q25; exact R25.
- rewrite Q26; exact R26.
- rewrite Q27; exact R27.
- rewrite Q3; exact R3.
- rewrite Q4; exact R4.
Qed.

#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK"] Lemma finish_nil : forall regs m,
RI regs -> LM m ->
realizes RSEGS (mkCfg (mkst regs (0x55270 : word) m (seg_rom RSEGS)) model) (t_emit [] K).
Proof. intros. apply rz_emit_nil. apply finish; assumption. Qed.

#[using="Type"] Lemma pc_53514 : v_addi (0x552ec : word) 4 = (0x552f0 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop1 : forall n regs m (k : nat) (b : word) (bs : list byte),
(length bs <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
(1 <= k < length bs)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
rdn RSEGS mem1 b (length bs) = Some bs ->
(bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
(bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
(Z.of_nat (length bs) <= 2 ^ 30)%Z ->
realizes RSEGS (mkCfg (mkst regs (0x552fc : word) m (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
Proof.
induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b) as Hb.

destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
(Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).

eapply (rz_writev1_wall RSEGS regs1 (0x552ec : word) m' model W_53510 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
[ exact F_53510 | exact E_53510 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
- subst m'. rdn_solve.
- subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
- rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
- unfold TASK_SIZE. u_norm. lia.
- unfold TASK_SIZE. u_norm. lia.
- u_norm. lia.
- u_norm. lia.
-
intros k' K1 K2. rewrite pc_53514. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
+
destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
* rewrite length_skipn. lia.
* eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* exact LMm'.
* exact P10.
* rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
* rewrite P18. gres. exact Q18.
* rewrite P19. gres. exact Q20.
* rewrite length_skipn. lia.
* subst m'. unfold at_. rdn_solve.
* subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
* rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
* unfold at_. rewrite length_skipn. u_norm. lia.
* unfold at_. rewrite length_skipn. u_norm. lia.
* rewrite length_skipn. lia.
Qed.

#[using="bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK"] Lemma loop2 : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
(length bs0 + length bs1 <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
(1 <= k < length bs0 + length bs1)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
(Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
realizes RSEGS (mkCfg (mkst regs (0x552fc : word) m (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
Proof.
induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
-
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_le k bs0 bs1 LE).
eapply (rz_writev2_wall RSEGS regs1 (0x552ec : word) m' model W_53510 fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
[ exact F_53510 | exact E_53510 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
+ subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
{ replace (length bs0 - k)%nat with 0%nat by lia.
rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
+ rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
subst m'. repeat rdn_peel1.
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_53514. rewrite length_app, length_skipn in K2.
destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
-- subst m'. repeat rdn_peel1. exact Mb1.
-- subst m'. repeat rdn_peel1. exact Mn1.
-- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
-- exact Bbs1.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- exact DISJ1.
-- exact NW1.
-- rewrite length_skipn. lia.
-
destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs1))
(Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
{ replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_ge k bs0 bs1) by lia.
eapply (rz_writev1_wall RSEGS regs1 (0x552ec : word) m' model W_53510 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
(Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
(skipn (k - length bs0) bs1) K);
[ exact F_53510 | exact E_53510 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' K1 K2. rewrite pc_53514. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
apply finish_nil; [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
rdn_solve.
-- rewrite length_skipn.
apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- rewrite length_skipn. lia.
Qed.

End Loop.
End FPGEN1.

Ltac wout1 :=
rewrite wbytes_outside;
[ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
constructor.
- intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
unfold mem_sw2. do 3 wout1.
rewrite (E x) by lia.
unfold mem_sw1. do 13 wout1. reflexivity.
- unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
eapply mem_grows_trans; [|exact G].
unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
apply mem_grows_refl.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
Qed.

#[using="Type"] Lemma pc_5348c : v_addi (0x55264 : word) 4 = (0x55268 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

#[using="Type"] Theorem ref_stdio_write :
forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
(pending extra : list byte) (K : TSet),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(0 < fd < 2147483648)%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
m_halted model = None -> m_vm_lazy model = [] ->
(0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS mem s (length extra) = Some extra ->
ret_ok ret ->
K [] ->
(forall regs' mem',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
sw_post mem su f bufp bufsz mem' ->
realizes RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst regs (0x551dc : word) mem (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hh Hlazy WBP WPhi
LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
pose proof SWF as SWF'. pose proof SSP as SSP'.
destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
{ rewrite <- LENE. symmetry. apply u64_roundtrip'. }

set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
{ subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x97e70) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }

assert (HK' : forall regs' m,
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
LM su mem1 m ->
realizes RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
{ intros. apply HK. all: try assumption.
eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
match goal with H : LM _ _ _ |- _ => exact H end. }
pose proof (finish_nil su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
pose proof (loop1 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
pose proof (loop2 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hfd Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
pose proof (LM_refl su mem1) as LM1.
destruct (Z.eq_dec wb wp) as [EQ|NEQ].
-
destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
subst wb.
destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?M _) _) _ =>
replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
rewrite Z.sub_diag in M96.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
destruct extra as [|x0 extra'].
+
cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
eapply (rz_writev1_zero RSEGS regs1 (0x55264 : word) mem1 model W_53488 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
[ exact F_53488 | exact E_53488 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | pose proof QMz4.rw_bytes_max_ge17; lia | ].
{ u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
{ unfold TASK_SIZE. u_norm. lia. }
{ unfold TASK_SIZE. lia. }
rewrite pc_5348c.
destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. exact HlZ. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
eapply (rz_writev1_wall RSEGS regs1 (0x55264 : word) mem1 model W_53488 fd
(Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
[ exact F_53488 | exact E_53488 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
* u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
* unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
* unfold TASK_SIZE. u_norm. lia.
* unfold TASK_SIZE. lia.
* cbn [length] in LENE. lia.
* lia.
* intros k K1 K2. rewrite pc_5348c.
destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
-- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. f_equal. lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(Z.of_nat (length (x0 :: extra'))))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
++ exact LM1.
++ exact P10.
++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
++ rewrite P18. gres. exact R18.
++ rewrite P19. gres. exact R19.
++ exact M88.
++ rewrite <- HlZ. exact M80.
++ exact Be.
-
destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
eapply (rz_writev2_wall RSEGS regs1 (0x55264 : word) mem1 model W_53488 fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
[ exact F_53488 | exact E_53488 | exact Hh | exact Hlazy | exact Hfd | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
+ u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
+ u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
+ u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
+ rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
+ unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k K1 K2. rewrite pc_5348c. rewrite length_app in K2.
destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
* destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. f_equal. lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
apply FIN; [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(wp - wb + bv_unsigned l))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact R22. }
{ lia. }
{ lia. }
{ lia. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LM1.
-- exact P10.
-- rewrite P22. gres. rewrite R22. f_equal. lia.
-- rewrite P18. gres. exact R18.
-- rewrite P19. gres. exact R19.
-- exact M104.
-- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
-- exact M88.
-- rewrite <- HlZ. exact M80.
-- exact Bp.
-- exact Be.
-- u_norm. lia.
-- u_norm. lia.
Qed.
End FPGEN2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
