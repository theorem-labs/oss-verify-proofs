(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition STDIO_WRITE_DEPTH : Z := 112.
#[using="Type"] Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.
#[using="Type"] Lemma zlength_skipn : forall {A} n (l : list A), zlength (skipn n l) = zlength l - Z.of_nat (Nat.min n (length l)).
Proof. intros A n l. unfold zlength. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=47821050258.4000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
#[using="Type"] Lemma iov_total_1 : forall b, iov_total [b] = zlength b.
Proof. intros b. unfold iov_total, zlength. cbn. rewrite app_nil_r. reflexivity. Qed.
#[using="Type"] Lemma iov_total_2 : forall a b, iov_total [a; b] = zlength a + zlength b.
Proof. intros a b. unfold iov_total, zlength. cbn. rewrite app_nil_r, length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010=62108319258.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section StdioWrite.
Context {St : Type}.
Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
/\ ssp_cells m' canary
/\ st' = st.
Section Body.
Variables (RNG : footprint) (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st : St) (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word).
Local Notation q := (bv_unsigned sp + -112).
Let POST := stdio_write_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(zlength s) lo canary m st.
Hypothesis FD : fd = 1 \/ fd = 2.
Hypothesis LO : lo <= bv_unsigned sp - STDIO_WRITE_DEPTH.
Hypothesis GLO : GLOBALS_TOP <= lo.
Hypothesis Fp0 : 0 <= Fp. Hypothesis FPLO : Fp + 232 <= lo.
Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
Hypothesis B0 : 0 <= B. Hypothesis BS0 : 0 <= bufsize. Hypothesis BUFLE : zlength buf <= bufsize. Hypothesis BShi : B + bufsize < 2^64.
Hypothesis S0 : 0 <= S < 2^64. Hypothesis Shi : S + zlength s <= 2^64.
Hypothesis SP47 : bv_unsigned sp < 2^47. Hypothesis B47 : B + bufsize <= 2^47. Hypothesis S47 : S + zlength s <= 2^47.
Hypothesis SEPS : s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S)).
Hypothesis SEPB : buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B)).
Hypothesis FC0 : rw_cells asegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail).
Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
Hypothesis SSP0 : ssp_cells m canary.
Hypothesis MI0 : mem_inv asegs m.
Hypothesis BUFB : bytes_at asegs m B (to_bytes buf).
Hypothesis SRC : bytes_at asegs m S (to_bytes s).
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RFP : rng RNG Fp 232.
Hypothesis RB : rng RNG B (zlength buf).
Hypothesis RS : rng RNG S (zlength s).
Hypothesis RIMG : rng_aimg RNG.
Definition frame (j0 : list byte) (w1 w2 w3 w4 : word) : list cell :=
[CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra].
Definition data_ok (p : Z) (l : list Z) : Prop :=
bytes_at asegs m p (to_bytes l)
/\ p + zlength l <= 2^47
/\ (l = [] \/ ((p + zlength l <= lo \/ bv_unsigned sp <= p) /\ (p + zlength l <= Fp + 32 \/ Fp + 64 <= p)))
/\ rng RNG p (zlength l).
#[using="Type"] Lemma data_ok_rng : forall p l, data_ok p l -> rng RNG p (Z.of_nat (length (to_bytes l))).
Proof. intros p l (_ & _ & _ & R). rewrite length_to_bytes. exact R. Qed.
#[using="Type"] Lemma data_ok_task : forall p l, data_ok p l -> p + Z.of_nat (length (to_bytes l)) <= 0x800000000000.
Proof. intros p l (_ & H & _). rewrite length_to_bytes. unfold zlength in H. exact H. Qed.
Definition iov_rel (iov : list (list Z)) (iovp iovcnt : Z) (w1 w2 w3 w4 : word) : Prop :=
match iov with
| [b] => iovp = q + 24 /\ iovcnt = 1 /\ w4 = Z_to_bv 64 (zlength b) /\ data_ok (bv_unsigned w3) b
| [a; b] => iovp = q + 8 /\ iovcnt = 2 /\ w2 = Z_to_bv 64 (zlength a) /\ w4 = Z_to_bv 64 (zlength b)
/\ data_ok (bv_unsigned w1) a /\ data_ok (bv_unsigned w3) b
/\ bv_unsigned w1 + zlength a < 2^64
| _ => False
end.
#[using="buf s LO FPLO"] Lemma data_ok_now : forall m1 p l,
data_ok p l -> munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 ->
bytes_at asegs m1 p (to_bytes l).
Proof.
intros m1 p l (BA & _ & SEP & _) MU. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
destruct SEP as [-> | [S1 S2]].
- apply bytes_at_nil. cbn in BB. Local Ltac2 Set LiaHints.tbl := fun () => "0020>31165936320.7347761750701.7600000400CS2BBS2LO4FPLO2S12S2".
lia.
- apply (bytes_at_transport _ _ _ m1 _ _ BA MU). cbn [disjoint_from]. rewrite length_to_bytes.
unfold zlength, STDIO_WRITE_DEPTH in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="buf s FPLO"] Lemma data_ok_skipn : forall p l k, data_ok p l -> 0 <= k <= zlength l -> data_ok (p + k) (skipn (Z.to_nat k) l).
Proof.
intros p l k (BA & T47 & SEP & RR) Hk. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>10755863404.7716256490497.7717718774308.7934019840975.7734245929091.7949058408312.7654969821204.7756850834073.7759309009393.7600000400800G00O00Y00Z00^00b010S2HkS2HkS4FPLO2S12Hk2NES3T472HkS2S22Hk2NESS2HkS2HkS3T472NE2BB2Hk".
split; [| split; [rewrite zlength_skipn; unfold zlength in *; lia| split]].
- rewrite to_bytes_skipn. replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by lia.
rewrite <- (firstn_skipn (Z.to_nat k) (to_bytes l)) in BA. apply bytes_at_app in BA as [_ BA].
rewrite length_firstn, length_to_bytes in BA.
replace (Nat.min (Z.to_nat k) (length l)) with (Z.to_nat k) in BA by (unfold zlength in Hk; lia).
exact BA.
- destruct (Z.eq_dec k (zlength l)) as [->|NE].
+ left. apply skipn_all2. unfold zlength. lia.
+ destruct SEP as [-> | [S1 S2]]. { exfalso. unfold zlength in *. cbn in *. lia. }
right. rewrite zlength_skipn. unfold zlength in *. split; lia.
- rewrite zlength_skipn. eapply rng_sub; [exact RR| lia| unfold zlength in *; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="buf s FPLO"] Lemma data_ok_skipn_w : forall p l k, data_ok p l -> 0 <= k <= zlength l -> p + k < 2^64 ->
data_ok (bv_unsigned (Z_to_bv 64 (p + k))) (skipn (Z.to_nat k) l).
Proof.
intros p l k D Hk LT. pose proof (bytes_at_bound _ _ _ _ (proj1 D)) as BB.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=5444331560.7500000:S2Hk2LT2BB".
rewrite unsigned_lit by lia. apply data_ok_skipn; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma frame_iov2 : forall m1 j0 w1 w2 w3 w4, rw_cells asegs m1 q (frame j0 w1 w2 w3 w4) ->
bytes_at asegs m1 (bv_unsigned sp + -104) (iovec_bytes [(w1, w2); (w3, w4)]).
Proof.
intros m1 j0 w1 w2 w3 w4 FR.
change (frame j0 w1 w2 w3 w4) with ([CB 8 j0] ++ [C8 w1; C8 w2; C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
cbn [cells_size csize Nat.add] in FR. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45674267130.75000001S".
replace (q + Z.of_nat 8) with (bv_unsigned sp + -104) in FR by lia.
eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
rewrite !app_nil_r, <- ?app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma frame_iov1 : forall m1 j0 w1 w2 w3 w4, rw_cells asegs m1 q (frame j0 w1 w2 w3 w4) ->
bytes_at asegs m1 (bv_unsigned sp + -88) (iovec_bytes [(w3, w4)]).
Proof.
intros m1 j0 w1 w2 w3 w4 FR.
change (frame j0 w1 w2 w3 w4) with ([CB 8 j0; C8 w1; C8 w2] ++ [C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
cbn [cells_size csize Nat.add] in FR. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62417289978.75000001S".
replace (q + Z.of_nat 24) with (bv_unsigned sp + -88) in FR by lia.
eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
rewrite !app_nil_r, <- ?app_assoc. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="LO GLO Fp0 FPLO FSEP1 FSEP2 RSTK RFP RIMG"] Lemma ok_path : forall (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 : word),
rw_cells asegs m1 q (frame j0 w1 w2 w3 w4) ->
rw_cells asegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m1 ssp_guard [C8 canary] ->
mem_inv asegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono asegs m m1 ->
stk asegs m1 lo q ->
evtF asegs RNG (POST tt st)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x8e840) fc None m1 (seg_rom asegs)).
Proof.
intros until x31. intros FR FC GOT GUARD MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00[0?11091651096.1021159692294.111 1162083372.109 1183002124.114 1263254915.109 13253656393.11214222305758.1141573081545.114 17776320428.10918246208652.11219507795017.11419882575240.11320134725086.11425071629079.11225071629079.11425518734025.11225878270252.10926279284492.11426325528707.10627366110558.11228487247198.11231546306377.11436115622444.10936447186568.11336781431939.10938258979550.11440420408451.1104253879427.110 43987951407.11044612541059.1114496343073.103 45098659203.10948475009685.10350201051337.11451678667181.10853767577772.10958817367046.11159431618270.11460172785283.11061383599491.11061917199021.10863235321901.1088940551555.110 00000100200600:00;00N00U00h00l01001501601=01>01?01D01H01L01M01T01[01`01d01e01f01m01n01o02302402502602:02M02Q02U02V02]02^02_02c02g02hSSS2LOS2HBSS2LO3GLO4FPLO5FSEP2S5FSEP2S2LO3GLO4FPLO5FSEP2S2LOS2HBS3Fp0SS5FSEP1SSS3Fp0S2LOS2HBSS5FSEP1S5FSEP2S3Fp0S2LOSSS5FSEP1SSS2LOSSSS2LOS2LO3GLO4FPLO5FSEP2S2LOS2LOSS5FSEP2SSS2LOS2LOS".
do 7 step.
do 3 step. if_false. do 10 step.
release_frame FR ST (bv_unsigned sp).
subst POST. unfold stdio_write_post, STDIO_WRITE_DEPTH, file_cells, ssp_cells, got_ssp, ssp_guard. sys_finish.
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac sysret_fast ret :=
zstep; zstep; zstep; zstep;
let Hr := fresh "Hr" in (if_cases Hr; zify_cond Hr); [ | exfalso; lia ];
zstep; replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
#[using="FD LO GLO Fp0 FPLO FSEP1 FSEP2 SP47 RSTK RFP RIMG"] Lemma loop_L2 : forall (fuel : nat) (iov : list (list Z)) (c : Z) (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word) (iovp iovcnt : Z)
(x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
iov_rel iov iovp iovcnt w1 w2 w3 w4 ->
rw_cells asegs m1 q (frame j0 w1 w2 w3 w4) ->
rw_cells asegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
rw_cells asegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m1 ssp_guard [C8 canary] ->
mem_inv asegs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono asegs m m1 ->
stk asegs m1 lo q ->
0 <= c < iov_total iov -> iov_total iov <= 67108864 ->
implAM RNG (stdio_write_loop fuel fd (iov_advance iov c)) st POST
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
(Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 iovcnt) (Z_to_bv 64 iovp) x20 (Z_to_bv 64 ssp_guard)
(Z_to_bv 64 (iov_total iov)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x8e8cc) fc None m1 (seg_rom asegs)).
Proof.
induction fuel as [|fuel IH]; intros until x31; intros IR FR FC GOT GUARD MI MU WM ST Hc TOT.
{ cbn [stdio_write_loop]. apply implAM_unr. }
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
Ltac cont IH total iov' FR FC GOT GUARD MI MU WM ST DATA :=
let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
replace (iov_total iov') with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
apply implAM_from_evt; sys_nret;
sysret_fast 0x8e8c4%Z;
zstep; zstep; (if_cases Keq; zify_cond Keq);
[ apply evtF_done; replace (ans =? iov_total iov') with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
apply implAM_ret;
eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST]
| apply evtF_done; replace (ans =? iov_total iov') with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
replace (Z_to_bv 64 total : word) with (Z_to_bv 64 (iov_total iov') : word)
by (f_equal; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
eapply (IH iov' _ mf j0 v1 v2 v3 v4) end;
first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
| rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia
| cbn [iov_rel]; DATA ] ].
destruct iov as [|a [|b [|? ?]]]; try contradiction.
-
rename a into b. destruct IR as (-> & -> & -> & DB).
pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB. rewrite length_to_bytes in BB.
change (Z.of_nat (length b)) with (zlength b) in BB.
rewrite iov_total_1 in *.
Local Ltac2 Set LiaHints.tbl := fun () => "03J0?11444581763.11411444581763.12011444581763.12511910133012.11413945494591.11414230027758.10914230027758.11414539528123.11315617080686.12015617080686.12516372718686.11616372718686.12117256834476.11817321373654.11617321373654.12117611149315.12017857850634.10917857850634.11418004552480.1151807047817.108 18292433221.12018378753154.10918378753154.11419446761366.10919446761366.1141984548469.109 1984548469.114 20313996398.12521585288942.11821585288942.12321729101182.12521816137573.11521816137573.12021962348140.11621962348140.1212204558782.116 2204558782.121 22094982803.10922094982803.11422194145798.10922194145798.11423734946939.11523734946939.12024531599015.12024531599015.12524559885216.12424559885229.11724730433221.11524730433221.12024732548164.11424732548164.11924929101479.12525071629079.11825071629079.12025071629079.12325071629079.12525203823395.10625203950530.11025952239477.11426344115696.11426344115696.11926362266742.12126362266742.12626733586808.11526733586808.12027399541823.11527399541823.12027408782881.12228886576219.12029126480746.12029128493451.11429377718491.11529379998266.10929459603221.10929459603221.11431339131998.10931339131998.11431385052042.10931385052042.11431847340711.11831847340711.12332534202715.11833626388012.11433628531917.12033680001082.11833680001082.12333890036513.11733890036513.12234329296772.12034349563011.12334990166189.12035484866318.1133734855790.125 38202574787.10938202574787.1143948558019.114 3971437694.120 3971437694.125 40091925664.11940091925664.12440091925677.11340104401007.10940104401007.11440196840212.10940196840212.11440728280371.10940728280371.11440928162421.12041527986692.10941527986692.11442363283422.1144242606947.115 4242606947.120 42464228004.12043570532452.10943570532452.11443725716909.12043727857484.11444459674051.11544461953826.10944535376654.11644535376654.12145099762158.12345221239098.12345462521482.11445659830526.11845659830526.12345797402170.114469426752.109  469426752.114  48037789822.1144821892890.114 48559260418.11348563437846.11548563437846.12049374088414.10949374088414.11450232731518.10950232731518.11450693720814.11850693720814.12352583566084.10952583566084.11453085287934.12353090748932.11454055154495.10954055154495.11454485784450.11454763372166.11454770104018.12454772201172.12154772201172.12254772201178.12354775866482.1135494439228.123 55162595506.10955333271071.10855333271071.11255336861632.11755336861632.12255336861646.11855336861646.12355338958790.12055338958790.12455345854354.10955345854354.11455420381985.10955420381985.11455460987188.11556145720764.12056145720764.125563227834.125  57297723570.12057745675194.12057745675194.12558718419528.11958718419528.12459308587409.11459308587409.11959308634759.10959308634759.11459321217802.10859321217802.11259498428761.1135955160707.118 5955160707.123 5968447876.115 5968447876.120 61674577390.12361895388678.12061897485824.11661897485824.11761897485824.12261906576978.10962175402556.11862175402556.12363728104341.10963728104341.11463920274819.11863920274819.1256406569415.114 6408840998.120 6495440936.120 65461747917.10965461747917.11465775799556.11466143077031.12367750960678.12268186327228.1258273157303.109 8273157303.114 8395091436.114 8937270820.122 9063607643.109 9063607643.114 9333008750.120 9333008750.125 9765216476.114 00000100200300@00F00G00H00P00X00`00a00b00l00m00n01701801901:01>01?01C01G01K01O01P01Q01Y01a01i02<02J02]02^02_02`02a02b02c02d02e03303F03G03H03L03P03_03n04=04L04M04N04O04P04Q04R04S04T04U04V04W04X04]04j05205?05C05D05K05R05V05Z05[05\05]05^05_05`05a05b05k06306;06A06G06K06O06P06Q06Z06[06c06d06e06f07907L07P07T07X07\07f08308@08A08B08M08N08O08P08X08m09809909:09C09L09S09Z09[09\09d09j09k0:>0:Q0:Z0:[0:\0:]0:^0:b0:f0;00;10;20;30;40;<0;D0;E0;F0;Y0;Z0;`0;f0;j0<=0<H0<[0<f0=60=F0=J0=K0=S0=[0=d0=m0>60>?0>H0>Q0>Z0>c0>d0>e0>i0>m0?10?70?A0?G0?M0?N0?O0?`0@70@>0@N0@[0@h0@n0@o0A00A10A20A:0AB0AJ0AR0A]0Ae0Ai0Am0An0Ao0B00B10B80B?0BM0BQ0BU0BV0BW0Bg0Bk0Bl0Bm0C70CE0CJ0CZ0Cb0Cj0D2SSSS2LO3GLO4SP47S4SP47FFS6NODROPS2LO3GLOS2LO3GLOFFS2Hc2Za2KdFFS2Hc4DROPFFFS2HcFS2LOS2LOS2FDS2FDFFS2LO3GLOS2LO3GLOS2LO3GLOS2LO3GLO4FPLO5FSEP2S2Hc5Hcase3KeqS2Hc4DROP5Hcase3KeqFFFFFFFFS2Hc5Hcase3KeqS2Hc4DROP5Hcase3KeqSSS2LOS2LOS2Hc4Hans5HcaseS2Hc4Hans5HcaseS2Hc4Hans5HcaseS2Hc4Hans5HcaseSSSSSSSFSSSSS3TOTS3TOT2Za4DROPS2Hc3KeqS2Hc4DROP3KeqS2LOFS2Hc2KdS2Hc2KdS2HcS2HcFFFFFFSSS2Hc4DROPS3LTA2KdS3LTA2KdS4SP47S4SP47S2LOS2LOSSS2Hc4DROPSS2LO3GLOSSSS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S2LOS2LOS2LOS2HcS2Hc2Za2KdS2LO3GLO4SP47S2LO3GLO4SP47FFS3TOT2Za2KdFFFS2Hc3TOTS2Hc3TOT2Za2Kd3LTA2BAS3LTA2Za2KdSSS2Hc4DROPS2Hc4DROPS2Hc2BBS2Hc2BBFFS2LO3GLOS4SP47FS2LO3GLO4FPLO5FSEP2S2LO3GLO4FPLO5FSEP2S2Hc4DROPFFFSS2HcS2HcS2Hc2Za2KdFFFFS2LO3GLOS2LO3GLOFFS2LO3GLO4FPLO5FSEP2FS4SP47S4SP47S2LOS2Hc3TOT2Za4DROP2ZbS3TOT2Za2ZbS2Hc3TOT2Za4DROP2ZbS3TOT2Za2ZbS2Hc3TOT2Za4DROPS2Hc3TOT2Za4DROPS2HBSS2Hc3TOTS2Hc3TOTS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegS2Hc4KnegFFS2HcS2HBS2HBS4SP47S2Hc2Za2KdS4SP47S4SP47SSS2Hc3TOT5Hcase2HrS2Hc3TOT2Za2Kd5Hcase2HrS2Hc2KdS4DROP2Kd6NODROPS2Hc3TOT4KnegS2Hc3TOT4KnegS4DROPSSSSS2LO3GLOS3TOT2ZbS3TOT2ZbS3TOT2ZbS3TOT2Za2ZbS3TOT2ZbS2HBS2HBFFSSS2Hc2BBS2Hc2BBS2Hc2Za2Kd3KeqS2FDS2FDFSS2Hc3TOT2Za4DROPS2HBFFS6NODROP1lS2Hc3TOT2Za2KdS3TOTS3TOT2Za4DROP2KdS2LO3GLOS2LO3GLOS4DROP1n".
assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
zstep. zstep.
replace (zlength b <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
change (iov_advance [b] c) with [skipn (Z.to_nat c) b].
do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
zstep. zstep. zstep. do 8 zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
step_ecall.
split.
{ at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
try (rewrite unsigned_lit by lia; cbn [map length]; lia).
1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
eexists [(_, _)]. split.
+ rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
+ constructor; [|constructor]. split; [| split; [| split]].
* cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
* cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))).
* cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia)) MU).
* cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))). }
cont IH (zlength b - c) [skipn (Z.to_nat c) b] FR FC GOT GUARD MI MU WM ST
ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
apply (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))).
-
destruct IR as (-> & -> & -> & -> & DA & DB & LTA).
pose proof (bytes_at_bound _ _ _ _ (proj1 DA)) as BA. pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB.
rewrite length_to_bytes in BA, BB.
change (Z.of_nat (length a)) with (zlength a) in BA. change (Z.of_nat (length b)) with (zlength b) in BB.
rewrite iov_total_2 in *.
assert (Za : 0 <= zlength a) by (unfold zlength; lia). assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
zstep. zstep.
destruct (Z.ltb_spec0 (zlength a) c) as [DROP|NODROP].
+
replace (zlength a <? c) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
replace (iov_advance [a; b] c) with [skipn (Z.to_nat (c - zlength a)) b]
by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [reflexivity|lia]).
do 5 zstep.
replace (Z.land 18446744073709551615 (zlength a)) with (zlength a)
by (change 18446744073709551615 with (2^64-1); rewrite zb_land_mask_l by lia; rewrite Z.mod_small by lia; reflexivity).
zstep. zstep. zstep. zstep. if_cases Kd; zify_cond Kd. { exfalso. lia. }
zstep. zstep.
do 8 zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
zstep. zstep. step_ecall.
split.
{ at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
try (rewrite unsigned_lit by lia; cbn [map length]; lia).
1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
eexists [(_, _)]. split.
+ rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
+ constructor; [|constructor]. split; [| split; [| split]].
* cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
* cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))).
* cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia)) MU).
* cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))). }
cont IH (zlength a + zlength b - c) [skipn (Z.to_nat (c - zlength a)) b] FR FC GOT GUARD MI MU WM ST
ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
apply (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))).
+
replace (zlength a <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
replace (iov_advance [a; b] c) with [skipn (Z.to_nat c) a; b]
by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [lia|reflexivity]).
do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
zstep. zstep. zstep. do 8 zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
step_ecall.
split.
{ at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
try (rewrite unsigned_lit by lia; cbn [map length]; lia).
1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
eexists [(_, _); (_, _)]. split.
+ rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
+ constructor; [|constructor; [|constructor]]; (split; [| split; [| split]]).
* cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
* cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia))).
* cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia)) MU).
* cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia))).
* cbn [snd]. rewrite length_to_bytes. reflexivity.
* cbn [fst]. apply (data_ok_task _ _ DB).
* cbn [fst]. apply (data_ok_now _ _ _ DB MU).
* cbn [fst]. exact (data_ok_rng _ _ DB). }
cont IH (zlength a + zlength b - c) [skipn (Z.to_nat c) a; b] FR FC GOT GUARD MI MU WM ST
ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
split; [reflexivity|]; split; [apply (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia)) | split; [exact DB| rewrite unsigned_lit by lia; rewrite zlength_skipn; unfold zlength in *; lia]]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="wend FD LO GLO Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE S0 SP47 B47 S47 SEPS SEPB FC0 ST0 SSP0 MI0 BUFB SRC RSTK RFP RB RS RIMG"] Lemma stdio_write_body : forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
implAM RNG (stdio_write (St:=St) fd buf s) st POST
(MS (mkR ra sp gp tp x5 x6 x7 s0i s1i (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) x13 x14 x15 x16 x17
s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x8e7ac) fc None m (seg_rom asegs)).
Proof.
intros.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
pose proof SSP0 as SSP. destruct SSP as [GOT GUARD]. pose proof FC0 as FC. pose proof ST0 as ST. pose proof MI0 as MI.
unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, file_cells in *.
pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
rewrite length_to_bytes in BB, BS. change (Z.of_nat (length buf)) with (zlength buf) in BB. change (Z.of_nat (length s)) with (zlength s) in BS.
Local Ltac2 Set LiaHints.tbl := fun () => "03T0?100583406.105  11444581763.1051162083372.104 11910081892.10612080262273.1051263254915.104 13322745511.10413518985818.10513716328399.10713945275471.10614013085244.10614086840430.10514230201758.10114230201758.10614916922350.10315617080686.10516372718686.10816372718686.11317321373654.10817321373654.11317366728278.10717776320428.10417857934714.10117857934714.10618378841330.10118909637614.10519446718438.10119446718438.1061974571836.103 1984599557.101 19882575240.10820038558908.10520313996398.10421155567546.10521585288942.10621729101182.10421816137573.11221890222206.10521962348140.10821962348140.1132204558782.108 2204558782.113 22094935779.10122094935779.10622163107130.10622193934966.10122193934966.10623734946939.11224427909389.91 24531599015.10524559885229.10324630998586.10524730433221.10724730433221.11224732548164.10624732548164.11124929101479.10425067826030.10525071629079.10325071629079.10425071629079.10525071629079.10625878270252.10425952052997.10626049497404.10626477173415.10326733586808.11226968004263.10526982344558.10527399541823.11227408782892.10427453056622.10427804035822.10629085018494.10529414937255.10629459646309.10129459646309.10629906675326.10530196181434.10530274919918.1063106004334.105 31339211822.10131339211822.10631385107450.10131651016162.10131653113715.10731757500965.11031847340711.10631913473429.98 32017482750.10332070795196.10532651489978.10433140611582.10633680001082.10633890036527.10534329296772.11234349563011.10535022110958.10535265982326.11335265982326.11835289769712.10635289769712.11136115622447.10536166524798.10436447186568.10836781431939.1033734855790.104 38098496572.10538168338087.10538202662835.10139400444670.1053948506803.106 3971437694.105 40091925676.10440196653924.10140420408451.10540623921831.10640728487235.10140728487235.1064093298670.103 41527906932.10142363469742.1064253879427.106 42619492738.11042621589898.10842621589899.10742628419649.11242628727976.10442630517456.10142630517456.10642849687948.10442852061172.10642857743526.11042859840686.10842859840687.10743055481388.95 43570612244.10143987951407.10544109304508.10444250622631.10544535376654.10844535376654.11344612541059.10645098659203.10545099762158.10545221239098.10545228683929.10745462347514.10645659830526.10646232973498.10546270630510.104469350960.101  469350960.106  48037746702.1064822099818.106 49374270638.10149691078311.10549746962786.90 49961654863.10250134779708.10550232688398.10150693720814.10651678667181.10352583650164.10153085287934.10553090964084.10653510313882.10853699986484.11253767577772.10454055365455.10154261855034.10354485602290.10654794350626.1075494439228.105 55420171089.10155420171089.1065543757023.112 55459467943.10555509061630.10556145720764.105563227834.104  56336554256.89 57637878894.10557745675194.10557839090926.10558718419528.11158718419528.11659308587409.10659308587409.11159308634497.10159308634497.10659314955108.1045955160707.106 5968447876.107 60172785283.10560330452198.97 61383599491.10561674577390.10561917199020.10462175402556.10663235321901.1026340307024.88  63728184293.10163728184293.10663920274819.10464302924052.10164302924052.10664305021829.10764305021829.11265461573821.10165461573821.10665518452462.10665775621492.10665805175866.10666143077031.10567802098942.10668186327228.1047779942894.106 783829358.105  8002142652.105 8166968988.107 8273069255.101 8273069255.106 8583720762.105 8927061985.112 8940551555.105 9063429419.106 9333008750.105 00000800900=00J00K00L00M00U00V00\00`00h00i00j01201:01;01<01=01>01C01G01H01I01M01U01Y01]01a01b01c01g01o02502=02P02b03503603703803903:03;03A03B03C03[03`03a03e03k04704P04\05505605>05?05@05A05B05F05G05K05L05R05S05[05`05d05l06406G06H06I06J06]06c06k07307407507607?07H07I07J07K07^07b07h08;08A08E08F08G08O08P08Q08R08S08W08j08k08l09409809909:09M09N09a09e0:20:30:40:50:60:>0:?0:@0:A0:M0:Y0:e0;70;I0;X0;j0<<0<N0<_0=00=A0=E0=F0=J0=N0=O0=P0=Q0=R0=S0=[0=a0=m0=n0>A0>G0>O0>P0>Q0>R0>S0>T0>U0>`0>a0>e0>f0>n0?20?30?F0?G0?H0?I0?M0?S0?Y0?]0?k0?o0@00@10@<0@=0@P0@T0@Z0@[0@c0@i0A10A20A30AH0Ad0Ah0B00B70B80B90B:0B;0B<0BD0BH0BL0BP0BQ0BR0BS0BT0BX0B\0B`0Bd0Bh0Bl0C40C50C;0C<0CO0CS0C[0Cc0Cg0D50D60D70D=0DJ0DK0DQ0DYS2LO3GLOSS2LOS2LO3GLO4SP47SSSS3XNZ2XRFS4SP47S2HBS2LO3GLOFFS2LO3GLOS2LO3GLOFFFFS3KeqS2LOFFS2LOS2LO3GLOS2FDS2FDS2HBFSS2HBS2LO3GLOS4SP47S2LO3GLOS2LO3GLO4FPLO5FSEP2S2Zb3XNZ2XR2Kb3KeqS2LO3GLO4FPLO5FSEP2FFFFFFS4SP47FFS2Zb3XNZ2XR2Kb5Hcase3KeqS3S47SS2LOS4SP47S4Hans5HcaseS2Zb3XNZ2XR2Kb4Hans5HcaseS4Hans5HcaseS2Zb3XNZ2XR2Kb4Hans5HcaseSS2LO3GLOSSSSS2LOFS2HBSS4LENSSS2LO3GLOS3KeqS2LOS2LO3GLOS2LO3GLOS2LO3GLO4FPLO5FSEP2SFFS2LO3GLO4FPLO5FSEP2S4SP47S2LO3GLOS2LO3GLOFFFS2Zb4LENSS2Zb4LENSSSSS2LO3GLO4FPLO5FSEP2S2HBS4SP47S2LO3GLO4FPLO5FSEP2S4SP47S2LOSSS2LO3GLOSSSSS2LOS2LO3GLO4FPLO5FSEP2SSS2LO3GLOS2HBSSS2LO3GLO4FPLO5FSEP2SS2LO3GLO4FPLO5FSEP2S2LOS2LO3GLO4SP47SSFFS2LO3GLOFFSS2B03BS03B47S2B03BS03B47S2B03BS03B47S2B05BUFLE3B473NB1S2B05BUFLE3B473NB1S2B03BS03B472KbS2B05BUFLE3B473NB1S5BUFLE3B472BB3NB1S5BUFLE3B472BB3NB1S5BUFLE3B472BB2ZbS5BUFLE3B472BB2ZbS5BUFLE3B472BB2ZbS2LOSS2LOS2HBSFFSSS2LO3GLOS4SP47S2Zb2Zs4LENSFS2LO3GLO4FPLO5FSEP2S4SP47S2LO3GLOFFFSFSS5BUFLE3B47SS2HBFS2LO3GLOS2LOFS2LO3GLO4FPLO5FSEP2FSFS2LOS4SP47S4SP47S2LOS2Zs5Hcase3KeqS2HBFFS5BUFLE3B47SS2LO3GLO4FPLO5FSEP2S2HBS4SP47SS2LO3GLOS4SP47S2LO3GLOSSS2Zb2Zs4LENS5Hcase2HrS2Zb4LENS3XNZ2XR2Kb5Hcase2HrS2KbS3NB12KbS3NB11ESSSSSS2LO3GLOS2LOS2HBS2LOSFFSS2S0S2S0S2S0S2S0S2FDS2FDS2LO3GLOFS4SP47SS2LO3GLO4FPLO5FSEP2S2HBS2LO3GLOS2LO3GLOS2HBS2Zs5Hcase3KeqFFS4SP47S2Zs4LENS3NB1SS4LENSS2LO3GLO".
assert (Zb : 0 <= zlength buf) by (unfold zlength; lia). assert (Zs : 0 <= zlength s) by (unfold zlength; lia).
assert (DBUF : data_ok B buf) by (split; [exact BUFB | split; [lia | split; [exact SEPB| exact RB]]]).
assert (DS : data_ok S s) by (split; [exact SRC | split; [lia | split; [exact SEPS| exact RS]]]).
change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
change (bytes_at asegs m B (to_bytes buf)) with (boxed (bytes_at asegs m B (to_bytes buf))) in BUFB.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold stdio_write, WRITE_MAX.
destruct (Z.ltb_spec0 67108864 (zlength buf + zlength s)) as [BIG|LENS]. { apply implAM_unr. }
apply Z.nlt_ge in LENS.
cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
carve_frame 112%nat ST.
do 12 zstep. do 13 zstep.
replace (B + zlength buf - B) with (zlength buf) in * by lia.
lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (j0 := j) in FR end.
Ltac cont0 total iov0 iovp iovcnt FR FC GOT GUARD MI MU WM ST DATA :=
let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
replace (iov_total iov0) with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
apply implAM_from_evt; sys_nret;
sysret_fast 0x8e83c%Z;
zstep; (if_cases Keq; zify_cond Keq);
[ apply evtF_done; replace (ans =? iov_total iov0) with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
let L := fresh "L" in
lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
pose proof (fun fuel x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 =>
loop_L2 fuel iov0 ans mf j0 v1 v2 v3 v4 iovp iovcnt x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31) as L end;
cbv beta in L; rewrite ?iov_total_1, ?iov_total_2 in L; unfold ssp_guard in L;
eapply L; clear L;
first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
| unfold zlength in *; lia
| cbn [iov_rel]; DATA ]
| apply evtF_done; replace (ans =? iov_total iov0) with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
apply implAM_ret;
eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST] ].
destruct buf as [|b0 buf'] eqn:Ebuf; rewrite <- ?Ebuf in *.
-
replace (zlength buf) with 0 in FR |- * by (rewrite Ebuf; reflexivity).
rewrite !Z.add_0_r, !Z.add_0_l. rewrite Z.lxor_nilpotent. change (Z.b2z (0 <? 0)) with 0.
zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. lia. }
zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
zstep. change (0 + 1) with 1. zstep. zstep. zstep. step_ecall.
split.
{ at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
try (rewrite unsigned_lit by lia; cbn [map length]; lia).
1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
eexists [(_, _)]. split.
+ rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
+ constructor; [|constructor]. split; [| split; [| split]].
* cbn [snd]. rewrite length_to_bytes. reflexivity.
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU).
* cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DS). }
cont0 (zlength s) [s] (bv_unsigned sp + -88) 1 FR FC GOT GUARD MI MU WM ST
ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; rewrite unsigned_lit by lia; exact DS).
-
assert (NB1 : 1 <= zlength buf) by (rewrite Ebuf; unfold zlength; cbn [length]; lia).
replace (match buf with [] => [s] | _ :: _ => [buf; s] end) with [buf; s] by (rewrite Ebuf; reflexivity).
assert (XNZ : Z.lxor (B + zlength buf) B <> 0).
{ intros E. rewrite <- (Z.add_0_r B) in E at 2. apply Z.lxor_eq in E. lia. }
pose proof (Z_lxor_range (B + zlength buf) B ltac:(lia) ltac:(lia)) as XR.
replace (0 <? Z.lxor (B + zlength buf) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zstep. if_cases Kb; zify_cond Kb. 1:{ exfalso. lia. }
zstep. zstep. zstep.
replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
zstep. change (1 + 1) with 2. zstep. zstep. zstep. step_ecall.
split.
{ at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
try (rewrite unsigned_lit by lia; cbn [map length]; lia).
1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
eexists [(_, _); (_, _)]. split.
+ rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
+ constructor; [|constructor; [|constructor]]; (split; [| split; [| split]]).
* cbn [snd]. rewrite length_to_bytes. reflexivity.
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DBUF).
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DBUF MU).
* cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DBUF).
* cbn [snd]. rewrite length_to_bytes. reflexivity.
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
* cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU).
* cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DS). }
cont0 (zlength buf + zlength s) [buf; s] (bv_unsigned sp + -104) 2 FR FC GOT GUARD MI MU WM ST
ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
rewrite !unsigned_lit by lia; split; [exact DBUF | split; [exact DS| unfold zlength in *; lia]]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Body.
#[using="Type"] Lemma stdio_write_spec :
forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
(buf s : list Z) (S lo : Z) (canary : word),
rw_cells asegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
bytes_at asegs m B (to_bytes buf) ->
bytes_at asegs m S (to_bytes s) ->
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
(fd = 1 \/ fd = 2) ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
ssp_cells m canary -> mem_inv asegs m ->
(0 <= Fp) -> (Fp + 232 <= lo) ->
(Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
(0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
(0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
(buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B))) ->
rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength buf) -> rng RNG S (zlength s) -> rng_aimg RNG ->
(bv_unsigned sp < 2^47) -> (B + bufsize <= 2^47) -> (S + zlength s <= 2^47) ->
implAM RNG (stdio_write (St:=St) fd buf s) st
(stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
(zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x8e7ac) fc None m (seg_rom asegs)).
Proof.
intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi S0 Shi SEPS SEPB RSTK RFP RB RS RIMG SP47 B47 S47.
eapply stdio_write_body; eassumption.
Qed.
End StdioWrite.
End CANSEC1.
