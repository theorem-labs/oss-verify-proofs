(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs Q0z1 QCiC Qpj5 QCNF QoNr QdZp Qu3b QnRU QteI QMPy QIG5 QC9y Qr5k QbPx_c1 QvG1 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import Q0z1.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QMPy. Import Qu3b.Mq0.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0.
Import QvG1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_2 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_4 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_5 := lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells asegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3374) fc None m (seg_rom asegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold gfile_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

Lemma arg_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap w a,
arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d|li|lu]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & SZ & D1 & D2 & D3 & D4 & D5). exists slack.
split; [|repeat (split; [first [assumption | lia]|]); exact D5].
eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap ws args,
args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
rw_cells asegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
rw_cells asegs m A (pre ++ mid ++ post).
Proof.
intros m A pre mid post [[Hwf Hb] Hw] WF.
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
split; [split|].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells asegs m B [CB 0 []].
Proof.
intros m B H0 H1. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition VF_FRAME : Z := 368.

Definition vf_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : word -> option byte) (j1 j2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0xd38c4) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0) a1
(Z_to_bv 64 (bv_unsigned sp + -368)) (Z_to_bv 64 (bv_unsigned sp + -272)) (Z_to_bv 64 (bv_unsigned sp + -104)) a5 a6 a7
(Z_to_bv 64 0x642ea0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -368)
[C8 a2; C8 a2; CB 80 j1; CB 168 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -368).

Lemma vf_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> band_lo <= lo -> mem_inv asegs m ->
rw_cells asegs m 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] -> rw_cells asegs m 0x642ea0 [C8 canary] ->
evt asegs (vf_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd385c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI SSP1 SSP2.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 368%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 26 (zstep; try (fix_litstore; mem_after_store_opt)).
apply evt_done. unfold vf_saves_post. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact ST].
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -368) _ |- _ => exact H end.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
bytes_at asegs m A (zb f).
Proof.
intros m A f MI RB H0 H1.
pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Qc6I.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QnRU.Mq4.
Import QIG5 Qr5k.Mq0 QbPx_c1.Mq0 Qi1S.Mq1.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
m s = Qc6I.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = Qc6I.Ret (Ok (tt, o ++ bs)).
Proof.
intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
m s = Qc6I.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
mpad OUT_sn c w l fl o = Qc6I.Ret (Ok (tt, o ++ concat ps)).
Proof.
intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
apply OUT_sn_eq. exact H.
Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
destruct a as [s|i|u|dd|li|lu].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
eapply conv_tail_sn; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (d_t d =? 99); [eapply conv_tail_sn; eassumption|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
- discriminate.
- destruct (negb (d_ty d =? T_LONG)); [discriminate|].
destruct (INTMAX_MAX <? li mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_ULONG) || negb (d_t d =? 117))%bool; [discriminate|].
eapply conv_int_sn; eassumption.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
printf_loop OUT_sn OUTFP_sn fuel s args cnt o = Qc6I.Ret (Ok (r, o ++ concat ps)).
Proof.
induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop].
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg o) as Ho.
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
printf_model OUT_sn OUTFP_sn fmt args [] = Qc6I.Ret (Ok (r, concat ps)).
Proof.
intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof.
intros x Hx. destruct (Z_lt_le_dec x 10).
- rewrite dec_digits_small by lia. rewrite Z.div_small, Z.mod_small, dec_digits_0 by lia. reflexivity.
- apply dec_digits_step. lia.
Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. intros x Hx. rewrite dec_digits_step1 by lia. rewrite length_app. cbn. lia. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof.
induction n as [|n IH]; intros x Hx H64.
- cbn in Hx. replace x with 0 by lia. rewrite dec_digits_0. cbn. lia.
- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite dec_digits_0; cbn; lia|].
rewrite dec_digits_step1 by lia. rewrite length_app. cbn [length].
specialize (IH (x / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)). lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Lemma zsub_snoc : forall l i n, 0 <= i -> 0 <= n -> i + n + 1 <= zlength l ->
zsub l i (n + 1) = zsub l i n ++ [znth l (i + n)].
Proof.
intros l i n Hi Hn H. unfold zsub, zlength in *.
replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
rewrite firstn_S_snoc by (rewrite length_skipn; lia). rewrite nth_skipn.
unfold znth. destruct (Z.ltb_spec0 (i + n) 0); [lia|].
replace (Z.to_nat (i + n)) with (Z.to_nat i + Z.to_nat n)%nat by lia. reflexivity.
Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. intros. reflexivity. Qed.

Lemma fmt_u_loop_dec : forall (n : nat) fuel y s b,
(n < fuel)%nat -> 0 <= y < 10 ^ Z.of_nat n -> y < 2^64 -> Z.of_nat n <= s -> s <= zlength b ->
exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - zlength (dec_digits y), b')
/\ length b' = length b
/\ zsub b' (s - zlength (dec_digits y)) (zlength (dec_digits y)) = dec_digits y
/\ (forall i, ~ (s - zlength (dec_digits y) <= i < s) -> znth b' i = znth b i).
Proof.
induction n as [|n IH]; intros fuel y s b Hf Hy Hy64 Hs Hb.
- cbn in Hy. destruct fuel as [|fuel]; [lia|]. exists b. cbn [fmt_u_loop].
replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
replace y with 0 by lia. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
- destruct fuel as [|fuel]; [lia|].
destruct (Z.eq_dec y 0) as [->|NZ].
+ exists b. cbn [fmt_u_loop Z.eqb negb]. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
+ cbn [fmt_u_loop]. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
unfold fmt_u_loop_body at 1.
rewrite Nat2Z.inj_succ in Hy, Hs. rewrite Z.pow_succ_r in Hy by lia.
destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10)) ltac:(lia)
ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)
ltac:(lia) ltac:(rewrite zlength_zupd; lia))
as (b' & E & LEN & SUB & OUT).
pose proof (dec_digits_step1 y ltac:(lia)) as DD.
assert (LD : zlength (dec_digits y) = zlength (dec_digits (y / 10)) + 1) by (rewrite DD, zlength_app; reflexivity).
pose proof (zlength_nonneg (dec_digits (y / 10))) as L0.
pose proof (dec_digits_len_bound n (y / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)) as L20.
unfold zlength in *.
exists b'. split; [rewrite E; f_equal; f_equal; f_equal; lia|].
split; [rewrite LEN; apply zupd_length|].
split.
* rewrite LD. replace (s - (Z.of_nat (length (dec_digits (y / 10))) + 1)) with (s - 1 - Z.of_nat (length (dec_digits (y / 10)))) by lia.
rewrite zsub_snoc by (unfold zlength; rewrite ?LEN, ?zupd_length; lia).
rewrite SUB. replace (s - 1 - Z.of_nat (length (dec_digits (y / 10))) + Z.of_nat (length (dec_digits (y / 10)))) with (s - 1) by lia.
rewrite OUT by lia. rewrite znth_zupd_eq by (unfold zlength; lia). rewrite DD. unfold CHR_0. reflexivity.
* intros i Hi. rewrite OUT by lia. apply znth_zupd_neq. lia.
Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_u_dec : forall x, 0 <= x < 2^64 ->
exists b', fmt_u x (zrepeat 0 24) 24 = Some (24 - zlength (dec_digits x), b')
/\ zlength b' = 24 /\ zsub b' (24 - zlength (dec_digits x)) (zlength (dec_digits x)) = dec_digits x.
Proof.
intros x Hx. unfold fmt_u. change FMT_U_FUEL with 21%nat.
destruct (fmt_u_loop_dec 20 21 x 24 (zrepeat 0 24) ltac:(lia) ltac:(pose proof pow10_20; lia) ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia) ltac:(change (zlength (zrepeat 0 24)) with 24; lia))
as (b' & E & LEN & SUB & _).
exists b'. rewrite E. split; [reflexivity|]. split; [unfold zlength; rewrite LEN; reflexivity| exact SUB].
Qed.

Ltac zb1 :=
match goal with
| |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
| |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
| |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
end; cbn [andb orb negb]; cbv beta iota.

Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. reflexivity. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. reflexivity. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. reflexivity. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

Lemma tail_pieces_d : forall prefix body, zlength prefix <= 1 -> 1 <= zlength body <= 20 ->
tail_pieces 0 0 0 (Z.max (-1) (zlength body + 0)) prefix body = Some ([prefix; body], zlength prefix + zlength body).
Proof.
intros prefix body Hp Hb. pose proof (zlength_nonneg prefix). unfold tail_pieces. cbv zeta.
replace (Z.max (Z.max (-1) (zlength body + 0)) (zlength body)) with (zlength body) by lia.
replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
unfold INT_MAX. zb1. zb1.
unfold pad_pieces. fl0. zb1. zb1. reflexivity.
Qed.

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Qc6I.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp.
Import QnRU.
Import QFy3 Qr5k.Mq3 QbPx_c1 Qi1S.Mq3.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
m s = Qc6I.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = Qc6I.Ret (Ok (tt, o ++ bs)).
Proof.
intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
m s = Qc6I.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
mpad OUT_sn c w l fl o = Qc6I.Ret (Ok (tt, o ++ concat ps)).
Proof.
intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
apply OUT_sn_eq. exact H.
Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
destruct a as [s|i|u|dd|li|lu].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
eapply conv_tail_sn; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (d_t d =? 99); [eapply conv_tail_sn; eassumption|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
- discriminate.
- destruct (negb (d_ty d =? T_LONG)); [discriminate|].
destruct (INTMAX_MAX <? li mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_ULONG) || negb (d_t d =? 117))%bool; [discriminate|].
eapply conv_int_sn; eassumption.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
printf_loop OUT_sn OUTFP_sn fuel s args cnt o = Qc6I.Ret (Ok (r, o ++ concat ps)).
Proof.
induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop].
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg o) as Ho.
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
printf_model OUT_sn OUTFP_sn fmt args [] = Qc6I.Ret (Ok (r, concat ps)).
Proof.
intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof.
intros x Hx. destruct (Z_lt_le_dec x 10).
- rewrite dec_digits_small by lia. rewrite Z.div_small, Z.mod_small, dec_digits_0 by lia. reflexivity.
- apply dec_digits_step. lia.
Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. intros x Hx. rewrite dec_digits_step1 by lia. rewrite length_app. cbn. lia. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof.
induction n as [|n IH]; intros x Hx H64.
- cbn in Hx. replace x with 0 by lia. rewrite dec_digits_0. cbn. lia.
- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite dec_digits_0; cbn; lia|].
rewrite dec_digits_step1 by lia. rewrite length_app. cbn [length].
specialize (IH (x / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)). lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Lemma zsub_snoc : forall l i n, 0 <= i -> 0 <= n -> i + n + 1 <= zlength l ->
zsub l i (n + 1) = zsub l i n ++ [znth l (i + n)].
Proof.
intros l i n Hi Hn H. unfold zsub, zlength in *.
replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
rewrite firstn_S_snoc by (rewrite length_skipn; lia). rewrite nth_skipn.
unfold znth. destruct (Z.ltb_spec0 (i + n) 0); [lia|].
replace (Z.to_nat (i + n)) with (Z.to_nat i + Z.to_nat n)%nat by lia. reflexivity.
Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. intros. reflexivity. Qed.

Lemma fmt_u_loop_dec : forall (n : nat) fuel y s b,
(n < fuel)%nat -> 0 <= y < 10 ^ Z.of_nat n -> y < 2^64 -> Z.of_nat n <= s -> s <= zlength b ->
exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - zlength (dec_digits y), b')
/\ length b' = length b
/\ zsub b' (s - zlength (dec_digits y)) (zlength (dec_digits y)) = dec_digits y
/\ (forall i, ~ (s - zlength (dec_digits y) <= i < s) -> znth b' i = znth b i).
Proof.
induction n as [|n IH]; intros fuel y s b Hf Hy Hy64 Hs Hb.
- cbn in Hy. destruct fuel as [|fuel]; [lia|]. exists b. cbn [fmt_u_loop].
replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
replace y with 0 by lia. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
- destruct fuel as [|fuel]; [lia|].
destruct (Z.eq_dec y 0) as [->|NZ].
+ exists b. cbn [fmt_u_loop Z.eqb negb]. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
+ cbn [fmt_u_loop]. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
unfold fmt_u_loop_body at 1.
rewrite Nat2Z.inj_succ in Hy, Hs. rewrite Z.pow_succ_r in Hy by lia.
destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10)) ltac:(lia)
ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)
ltac:(lia) ltac:(rewrite zlength_zupd; lia))
as (b' & E & LEN & SUB & OUT).
pose proof (dec_digits_step1 y ltac:(lia)) as DD.
assert (LD : zlength (dec_digits y) = zlength (dec_digits (y / 10)) + 1) by (rewrite DD, zlength_app; reflexivity).
pose proof (zlength_nonneg (dec_digits (y / 10))) as L0.
pose proof (dec_digits_len_bound n (y / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)) as L20.
unfold zlength in *.
exists b'. split; [rewrite E; f_equal; f_equal; f_equal; lia|].
split; [rewrite LEN; apply zupd_length|].
split.
* rewrite LD. replace (s - (Z.of_nat (length (dec_digits (y / 10))) + 1)) with (s - 1 - Z.of_nat (length (dec_digits (y / 10)))) by lia.
rewrite zsub_snoc by (unfold zlength; rewrite ?LEN, ?zupd_length; lia).
rewrite SUB. replace (s - 1 - Z.of_nat (length (dec_digits (y / 10))) + Z.of_nat (length (dec_digits (y / 10)))) with (s - 1) by lia.
rewrite OUT by lia. rewrite znth_zupd_eq by (unfold zlength; lia). rewrite DD. unfold CHR_0. reflexivity.
* intros i Hi. rewrite OUT by lia. apply znth_zupd_neq. lia.
Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_u_dec : forall x, 0 <= x < 2^64 ->
exists b', fmt_u x (zrepeat 0 24) 24 = Some (24 - zlength (dec_digits x), b')
/\ zlength b' = 24 /\ zsub b' (24 - zlength (dec_digits x)) (zlength (dec_digits x)) = dec_digits x.
Proof.
intros x Hx. unfold fmt_u. change FMT_U_FUEL with 21%nat.
destruct (fmt_u_loop_dec 20 21 x 24 (zrepeat 0 24) ltac:(lia) ltac:(pose proof pow10_20; lia) ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia) ltac:(change (zlength (zrepeat 0 24)) with 24; lia))
as (b' & E & LEN & SUB & _).
exists b'. rewrite E. split; [reflexivity|]. split; [unfold zlength; rewrite LEN; reflexivity| exact SUB].
Qed.

Ltac zb1 :=
match goal with
| |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
| |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
| |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
end; cbn [andb orb negb]; cbv beta iota.

Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. reflexivity. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. reflexivity. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. reflexivity. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

Lemma tail_pieces_d : forall prefix body, zlength prefix <= 1 -> 1 <= zlength body <= 20 ->
tail_pieces 0 0 0 (Z.max (-1) (zlength body + 0)) prefix body = Some ([prefix; body], zlength prefix + zlength body).
Proof.
intros prefix body Hp Hb. pose proof (zlength_nonneg prefix). unfold tail_pieces. cbv zeta.
replace (Z.max (Z.max (-1) (zlength body + 0)) (zlength body)) with (zlength body) by lia.
replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
unfold INT_MAX. zb1. zb1.
unfold pad_pieces. fl0. zb1. zb1. reflexivity.
Qed.

End Mq2.

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbPx_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbPx_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_2 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_4 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_5 := lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells asegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a38) fc None m (seg_rom asegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold gfile_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

Lemma arg_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap w a,
arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d|li|lu]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & SZ & D1 & D2 & D3 & D4 & D5). exists slack.
split; [|repeat (split; [first [assumption | lia]|]); exact D5].
eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap ws args,
args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
rw_cells asegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
rw_cells asegs m A (pre ++ mid ++ post).
Proof.
intros m A pre mid post [[Hwf Hb] Hw] WF.
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
split; [split|].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells asegs m B [CB 0 []].
Proof.
intros m B H0 H1. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition VF_FRAME : Z := 368.

Definition vf_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : word -> option byte) (j1 j2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0xd5f88) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0) a1
(Z_to_bv 64 (bv_unsigned sp + -368)) (Z_to_bv 64 (bv_unsigned sp + -272)) (Z_to_bv 64 (bv_unsigned sp + -104)) a5 a6 a7
(Z_to_bv 64 0x645560) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -368)
[C8 a2; C8 a2; CB 80 j1; CB 168 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -368).

Lemma vf_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> band_lo <= lo -> mem_inv asegs m ->
rw_cells asegs m 0xe8f90 [C8 (Z_to_bv 64 0x645560)] -> rw_cells asegs m 0x645560 [C8 canary] ->
evt asegs (vf_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5f20) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI SSP1 SSP2.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 368%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 26 (zstep; try (fix_litstore; mem_after_store_opt)).
apply evt_done. unfold vf_saves_post. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact ST].
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -368) _ |- _ => exact H end.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
bytes_at asegs m A (zb f).
Proof.
intros m A f MI RB H0 H1.
pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
