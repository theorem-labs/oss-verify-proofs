(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the trim loop of segment S03 (TRIM, 0x8cffc-0x8d06c) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (interface lib/B/Prog/verbs_receive_iface.v). The B twin of
   lib/A/Prog/verbs_receive_s03_k.v (A's 0x8d624 loop): the same invariant, run on B's re-laid loop.

   The loop head 0x8d014 walks the line q[0, l) backwards from its last byte: a1 is the cursor q + j, a0 = a1 - 1 the
   byte it reads, a2 = 1, a3 = 32 and a4 = 0x100002600 (the bits of '\t', '\n', '\r' and ' '). One pass:
   - 0x8d014 `beq a1,a2,0x8d938`, B only (UBSan: the pointer a1 - 1 would be null): never taken, since a1 = q + j
     >= 4097 (the run decides it from atom 11's range);
   - 0x8d018-0x8d024 the inline check of the byte at a0 (`bnez a6,0x8d058`, B only; slow block 0x8d058-0x8d060 in the
     block's last, partial granule, its report 0x8d998 not reached);
   - 0x8d028-0x8d03c a1 -= 1, the byte load, `bltu a3,a6` (leaves for 0x8d070 when the byte is above 32), the mask test
     (leaves for 0x8d070 when the byte is not a trailing blank);
   - 0x8d040-0x8d048 the inline check of the store (slow block 0x8d064-0x8d06c) and `sb zero,0(a1)`;
   - 0x8d04c-0x8d054 a0 -= 1, the back edge `bltu s2,a1,0x8d014` while q < q + j - 1, else `j 0x8d070`.
   One symbolic run per branch executes the pass from a state seeded with a1 = atom 11, the byte = atom 32 and q's
   shadow entry; the passes are chained by induction on j (the plain proof's trim_loop,
   lib/Prog/verbs_receive_trim.v:94-163, has the same invariant: the bytes at q are firstn j U ++ zeros ++ [0] and
   trim U = trim (firstn j U)). The ASan checks are the shadow tokens of the symbolic run (tok_load / tok_branch);
   their obligations are the line block's addressable bytes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_trim.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaSB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PVT := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_trim.

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic state at the loop head 0x8d014 (listing offset 27364): a1 = atom 11 (the cursor q + j), a0 = a1 - 1,
   a2 = 1, a3 = 32, a4 = 0x100002600; the byte at a1 - 1 is atom 32. The shadow entry of atom 11 over [-1, 0) only
   says the byte is application memory (the cells check of the window); its addressability is the run's obligation. *)
Definition vr3_regs : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SOff 11 (-1))) (Z_to_bv 5 12) (SLit 1)) (Z_to_bv 5 13) (SLit 32))
  (Z_to_bv 5 14) (SLit 4294977024).
Definition vr3_rgn : YP09.region :=
YP09.mkRegion (Some 11%nat) (-1) 0 (-1) 0 [YP09.mkChunk (-1) (CVal 1 (SOff 32 0))].
Definition vr3_G : facts :=
mkFacts [(19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, mkAF 4097 140737479966720 0); (32%nat, mkAF 0 255 0)] [] [].
Definition vr3_ss : sstate := mkSS 27364 vr3_regs [vr3_rgn] None vr3_G.
Definition vr3_SH : list shent := [mkSHE 11 0 (-1)].
Definition vr3_Bx : sv := SOff 19 0.
Definition vr3_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the registers the loop keeps (sp, gp, tp, s0 .. s11) *)
Definition vr3_keepz : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* ---------------------------------------------------------------------------------------------------------------
   The bytes of the line block during the loop, and the trim facts *)
Definition vr3_bytes (U : list byte) (j : nat) : list byte :=
firstn j U ++ repeat (Z_to_bv 8 0) (length U - j) ++ [Z_to_bv 8 0].

Lemma vr3_bytes_len : forall U j, (j <= length U)%nat -> length (vr3_bytes U j) = S (length U).
Proof.
intros U j Hj. unfold vr3_bytes. rewrite !length_app, length_firstn, repeat_length. cbn [length]. lia.
Qed.

Lemma vr3_nth_zeros : forall n m, nth n (repeat (Z_to_bv 8 0) m ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
intros n m. destruct (Nat.lt_ge_cases n (length (repeat (Z_to_bv 8 0) m ++ [Z_to_bv 8 0]))) as [Hn|Hn];
  [|apply nth_overflow; exact Hn].
pose proof (nth_In _ (Z_to_bv 8 0) Hn) as Hin. apply in_app_or in Hin as [Hin|[Hin|[]]];
  [exact (repeat_spec _ _ _ Hin) | symmetry; exact Hin].
Qed.

Lemma vr3_bytes_nth : forall U j i, (j <= length U)%nat ->
nth i (vr3_bytes U j) (Z_to_bv 8 0) = if (i <? j)%nat then nth i U (Z_to_bv 8 0) else Z_to_bv 8 0.
Proof.
intros U j i Hj. unfold vr3_bytes.
destruct (Nat.ltb_spec i j) as [Hi|Hi].
- rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn j U) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
- rewrite app_nth2 by (rewrite length_firstn; lia). apply vr3_nth_zeros.
Qed.

Lemma vr3_firstn_S : forall (U : list byte) j, (j < length U)%nat ->
firstn (S j) U = firstn j U ++ [nth j U (Z_to_bv 8 0)].
Proof. intros U j Hj. apply PVT.firstn_S_snoc. apply nth_error_nth'. exact Hj. Qed.

Lemma vr3_trim_t : forall P b, PV.is_trail b = true -> PV.trim (P ++ [b]) = PV.trim P.
Proof. intros P b H. exact (PVT.trim_snoc_t P b H). Qed.
Lemma vr3_trim_k : forall P b, PV.is_trail b = false -> PV.trim (P ++ [b]) = P ++ [b].
Proof. intros P b H. exact (PVT.trim_snoc_k P b H). Qed.

(* a list that differs from an old one at one index, read at the old one's bytes but there *)
Lemma vr3_abytes_upd1 : forall (rd rd' : reader) q (l l' : list byte) (i0 : nat) (v : byte),
abytes_atR rd q l -> length l' = length l -> (i0 < length l)%nat ->
(forall i, (i < length l)%nat -> i <> i0 -> nth i l' (Z_to_bv 8 0) = nth i l (Z_to_bv 8 0)) ->
(forall i, (i < length l)%nat -> i <> i0 -> rd' (q + Z.of_nat i) = rd (q + Z.of_nat i)) ->
nth i0 l' (Z_to_bv 8 0) = v -> rd' (q + Z.of_nat i0) = Some (bv_unsigned v) ->
abytes_atR rd' q l'.
Proof.
intros rd rd' q l l' i0 v H Hlen Hi0 Hn Hr Hv Hrv i Hi. rewrite Hlen in Hi.
destruct (Nat.eq_dec i i0) as [->|Hne]; [rewrite Hv; exact Hrv|].
rewrite (Hr i Hi Hne), (Hn i Hi Hne). exact (H i Hi).
Qed.

Lemma vr3_le1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* the trailing-blank test of the code: (0x100002600 >> b) & 1, its shift amount the low 6 bits of b *)
Lemma vr3_bit : forall E v, ew E 32 = Z_to_bv 64 v -> 0 <= v < 256 ->
U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 32 0)) (SLit 1)) = Z.land (Z.shiftr 4294977024 (v mod 64)) 1.
Proof.
intros E v H Hv. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 32 v H) by lia.
rewrite (zcanon_id 4294977024) by (unfold M64; lia).
replace (Z.land v 63) with (v mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
assert (Hm : 0 <= v mod 64 < 64) by (apply Z.mod_pos_bound; lia).
rewrite zcanon_id; [reflexivity|].
rewrite Z.shiftr_div_pow2 by lia.
assert (Hp : 0 < 2 ^ (v mod 64)) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ 4294977024); [apply Z.div_le_upper_bound; nia | unfold M64; lia].
Qed.

Ltac vr3_bvne := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X.
Ltac vr3_env HS := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => constr:(Ex) end.
Ltac vr3_md md' := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  set (md' := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody md' end.
Ltac vr3_ms HS m' := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into m' end.
(* a run keeps every byte but the one at q + j - 1, the window of the loop's region *)
Ltac vr3_Kp HFr E11 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
  intros a Ha Hne;
  lazymatch type of Hne with a <> ?X =>
  apply (kept_of_frame _ _ _ _ _ (fun x => x = X) HFr); [|exact Ha|exact Hne];
  let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq0 := fresh "Hq0" in
  intros b0 wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq0 | []]; injection Hq0 as <- <- <-;
  cbn [base_val] in Hrr; rewrite ?ew_ewset_other in Hrr by lia; rewrite E11 in Hrr; unfold w64 in Hrr;
  rewrite unsigned_lit_small in Hrr by lia; lia end.
Ltac vr3_ew E := rewrite ?ew_ewset_other by lia; exact E.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vr3_rd_val1 : forall H mem a v, val_mem SEGS (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview SEGS H mem a = Some v.
Proof.
intros H mem a v Hv Hr. pose proof (Hv 0%nat ltac:(lia)) as H0. replace (a + Z.of_nat 0) with a in H0 by lia.
unfold aview. rewrite H0. cbn [option_map]. f_equal. rewrite vr3_le1 by exact Hr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Lemma vr3_val1_of_rd : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Ha kk Hk. assert (kk = 0%nat) by lia. subst kk. replace (a + Z.of_nat 0) with a by lia.
destruct (aview_byte SEGS H mem a v Ha) as (b & Hm & Hbv & Hr). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, vr3_le1 by exact Hr. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by exact Hr. symmetry. exact Hbv.
Qed.

Lemma vr3_kept_of : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok_pi E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.

(* the byte of the loop's region at a state of the run *)
Lemma vr3_byte_at : forall (W : world SEGS) Ex ss (ms' : machine_state) cs e n v,
st_ok_pi SEGS VAL Ex ss (restrict (w_H W) ms') ->
ss_mem ss = [YP09.mkRegion (Some 11%nat) (-1) 0 (-1) 0 cs] ->
In (YP09.mkChunk (-1) (CVal 1 e)) cs ->
ew Ex 11 = w64 n -> 0 <= n < 2 ^ 64 -> U Ex e = v -> 0 <= v < 256 ->
rdW W (ms_mem ms') (n - 1) = Some v.
Proof.
intros W Ex ss ms' cs e n v HS Hm Hc H11 Hn He Hv.
assert (Hn0 : nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 11%nat) (-1) 0 (-1) 0 cs)) by (rewrite Hm; reflexivity).
pose proof (st_ok_pi_region_nth Ex ss _ 0 _ HS Hn0) as Hr. cbn [ms_mem restrict] in Hr.
assert (Hb : bv_unsigned (ew Ex 11) = n) by (rewrite H11; unfold w64; apply unsigned_lit_small; exact Hn).
pose proof (field_of_region_any Ex _ 11 n cs (-1) 0 (-1) 0 (-1) 1%N e Hr Hb Hc ltac:(lia)) as V.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V.
change (bv_unsigned (sv_denot Ex e)) with (U Ex e) in V. rewrite He, (Z.mod_small v 256 Hv) in V.
replace (n - 1) with (n + -1) by lia.
apply vr3_rd_val1; [exact V | exact Hv].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

Section loop.
Variables (W : world SEGS) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (k : Z)
  (q : Z) (U : list byte) (regs0 : bvmap 5 word) (memA : word -> option byte).
Hypothesis HIN : In (q, Z.of_nat (length U) + 1) (ablocks B lyc Sc).
Hypothesis HNEW : ~ In (q, Z.of_nat (length U) + 1) (ablocks B ly S).
Hypothesis H19 : getr regs0 (Z_to_bv 5 19) = w64 SHADOW_OFF.
Hypothesis H18 : getr regs0 (Z_to_bv 5 18) = w64 q.

Definition vr3_kept (regs : bvmap 5 word) : Prop :=
forall r, In r vr3_keepz -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Definition vr3_frame (mem : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + Z.of_nat (length U)) -> rdW W mem a = rdW W memA a.
(* the state at the loop head, j bytes still to test *)
Definition vr3_inv (j : nat) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
(1 <= j <= length U)%nat /\
getr regs (Z_to_bv 5 10) = w64 (q + Z.of_nat j - 1) /\ getr regs (Z_to_bv 5 11) = w64 (q + Z.of_nat j) /\
getr regs (Z_to_bv 5 12) = w64 1 /\ getr regs (Z_to_bv 5 13) = w64 32 /\ getr regs (Z_to_bv 5 14) = w64 4294977024 /\
vr3_kept regs /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
vr3_frame mem /\
abytes_atR (rdW W mem) q (vr3_bytes U j) /\ PV.trim U = PV.trim (firstn j U).
(* the state at the exit 0x8d070 (listing offset 27456): the line is trimmed in place *)
Definition vr3_out (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
vr3_kept regs /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k /\
vr3_frame mem /\
abytes_atR (rdW W mem) q (PV.trim U ++ repeat (Z_to_bv 8 0) (length U - length (PV.trim U)) ++ [Z_to_bv 8 0]).
Definition vr3_Q (W' : world SEGS) (c' : config) : Prop :=
W' = W /\ exists regs mem md,
c' = mkCfg (mkst regs (Z_to_bv 64 (BASE + 27456)) mem (seg_rom SEGS)) md /\ vr3_out regs mem md.

Lemma vr3_req : req_size (Z.of_nat (length U) + 1) = Z.of_nat (length U) + 1.
Proof. unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length U) + 1) 0); lia. Qed.

Lemma vr3_blk : forall memx mdx, AR SEGS B lyc Sc W memx mdx ->
4096 <= q /\ q + Z.of_nat (length U) + 1 <= alloc_ceiling /\
(forall a, q <= a < q + Z.of_nat (length U) + 1 -> apresent (w_H W) memx a).
Proof.
intros memx mdx HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HIN) as (_ & Hq4 & Hqc & _ & Hqpres & _).
rewrite vr3_req in Hqc, Hqpres. split; [exact Hq4|]. split; [lia|].
intros a Ha. exact (proj1 (Hqpres a ltac:(lia))).
Qed.

Lemma vr3_awr : forall (j : nat) Ex rs cs, (1 <= j <= length U)%nat -> 0 <= q -> q + Z.of_nat (length U) + 1 < 2 ^ 64 ->
rs = [YP09.mkRegion (Some 11%nat) (-1) 0 (-1) 0 cs] -> ew Ex 11 = w64 (q + Z.of_nat j) ->
awr_ok SEGS B Ex rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own.
Proof.
intros j Ex rs cs Hj Hq0 Hq1 -> H11 a (r & Hr & Ha). destruct Hr as [<- | []].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite H11 in Ha. unfold w64 in Ha.
rewrite unsigned_lit_small in Ha by lia.
right; right; left. exists q, (Z.of_nat (length U) + 1). split; [exact HIN|]. split; [exact HNEW|].
rewrite vr3_req. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The memory and register facts of one pass, without the symbolic states *)
Lemma vr3_kept_step : forall regs regs', vr3_kept regs ->
(forall r, In r vr3_keepz -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> vr3_kept regs'.
Proof. intros regs regs' HK KR r Hr. rewrite (KR r Hr). exact (HK r Hr). Qed.

Lemma vr3_frame_step : forall (j : nat) mem mem', (1 <= j <= length U)%nat -> vr3_frame mem ->
(forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W mem' a = rdW W mem a) -> vr3_frame mem'.
Proof. intros j mem mem' Hj HF KM a Ha Hout. rewrite (KM a Ha) by lia. exact (HF a Ha Hout). Qed.

(* a pass that leaves the byte at q + j - 1 as it was *)
Lemma vr3_keep_bytes : forall (j : nat) mem mem', (1 <= j <= length U)%nat ->
abytes_atR (rdW W mem) q (vr3_bytes U j) -> 0 <= q -> q + Z.of_nat (length U) < 2 ^ 64 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W mem' a = rdW W mem a) ->
rdW W mem' (q + Z.of_nat j - 1) = Some (bv_unsigned (nth (pred j) U (Z_to_bv 8 0))) ->
abytes_atR (rdW W mem') q (vr3_bytes U j).
Proof.
intros j mem mem' Hj HBy Hq0 Hq1 KM BY.
apply (vr3_abytes_upd1 (rdW W mem) (rdW W mem') q (vr3_bytes U j) (vr3_bytes U j) (pred j)
  (nth (pred j) U (Z_to_bv 8 0)) HBy eq_refl).
- rewrite vr3_bytes_len by lia. lia.
- intros i _ _. reflexivity.
- intros i Hi Hne. rewrite vr3_bytes_len in Hi by lia. apply KM; lia.
- rewrite vr3_bytes_nth by lia. replace ((pred j <? j)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity.
- replace (q + Z.of_nat (pred j)) with (q + Z.of_nat j - 1) by lia. exact BY.
Qed.

(* a pass that clears the trailing blank at q + j - 1 *)
Lemma vr3_store_bytes : forall (j : nat) mem mem', (1 <= j <= length U)%nat ->
abytes_atR (rdW W mem) q (vr3_bytes U j) -> PV.trim U = PV.trim (firstn j U) ->
PV.is_trail (nth (pred j) U (Z_to_bv 8 0)) = true -> 0 <= q -> q + Z.of_nat (length U) < 2 ^ 64 ->
(forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W mem' a = rdW W mem a) ->
rdW W mem' (q + Z.of_nat j - 1) = Some 0 ->
abytes_atR (rdW W mem') q (vr3_bytes U (pred j)) /\ PV.trim U = PV.trim (firstn (pred j) U).
Proof.
intros j mem mem' Hj HBy HT Tb Hq0 Hq1 KM BY. split.
- apply (vr3_abytes_upd1 (rdW W mem) (rdW W mem') q (vr3_bytes U j) (vr3_bytes U (pred j)) (pred j)
    (Z_to_bv 8 0) HBy).
  + rewrite !vr3_bytes_len by lia. reflexivity.
  + rewrite vr3_bytes_len by lia. lia.
  + intros i Hi Hne. rewrite vr3_bytes_len in Hi by lia. rewrite !vr3_bytes_nth by lia.
    destruct (Nat.ltb_spec i (pred j)) as [H1|H1]; destruct (Nat.ltb_spec i j) as [H2|H2]; try reflexivity; lia.
  + intros i Hi Hne. rewrite vr3_bytes_len in Hi by lia. apply KM; lia.
  + rewrite vr3_bytes_nth by lia. rewrite Nat.ltb_irrefl. reflexivity.
  + replace (q + Z.of_nat (pred j)) with (q + Z.of_nat j - 1) by lia. exact BY.
- rewrite HT. replace j with (Datatypes.S (pred j)) at 1 by lia. rewrite vr3_firstn_S by lia. apply vr3_trim_t. exact Tb.
Qed.

Lemma vr3_out_of : forall (j : nat) regs mem md, (j <= length U)%nat ->
vr3_kept regs -> ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k -> vr3_frame mem ->
abytes_atR (rdW W mem) q (vr3_bytes U j) -> PV.trim U = firstn j U -> vr3_out regs mem md.
Proof.
intros j regs mem md Hj HK HJ HF HBy HTU.
split; [exact HK|]. split; [exact HJ|]. split; [exact HF|].
rewrite HTU, length_firstn. replace (Nat.min j (length U)) with j by lia. exact HBy.
Qed.

Lemma vr3_trim_keep : forall (j : nat), (1 <= j <= length U)%nat -> PV.trim U = PV.trim (firstn j U) ->
PV.is_trail (nth (pred j) U (Z_to_bv 8 0)) = false -> PV.trim U = firstn j U.
Proof.
intros j Hj HT Tb. rewrite HT. replace j with (Datatypes.S (pred j)) by lia. rewrite vr3_firstn_S by lia.
apply vr3_trim_k. exact Tb.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The seed of one pass *)
Lemma vr3_seed : forall j regs mem md, vr3_inv j regs mem md ->
exists E, img_env VAL A_LIM E /\
env_agree 32 (Ereg regs [w64 (bv_unsigned (nth (pred j) U (Z_to_bv 8 0)))]) E /\
ew E 11 = w64 (q + Z.of_nat j) /\ ew E 19 = w64 SHADOW_OFF /\ ew E 18 = w64 q /\
ew E 32 = w64 (bv_unsigned (nth (pred j) U (Z_to_bv 8 0))) /\
st_ok_pi SEGS VAL E vr3_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 27364)) mem (seg_rom SEGS))) /\
sh_ok SEGS vr3_Bx vr3_SH E (mrestrict (w_H W) mem).
Proof.
intros j regs mem md (Hj & R10 & R11 & R12 & R13 & R14 & HK & HJ & HF & HBy & HT).
remember (nth (pred j) U (Z_to_bv 8 0)) as b eqn:Hb.
pose proof (bv_unsigned_in_range 8 b) as Hv. change (bv_modulus 8) with 256 in Hv.
pose proof (proj1 HJ) as HAR.
destruct (vr3_blk mem md HAR) as (Hq4 & Hqc & Hqpres).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hby : rdW W mem (q + Z.of_nat j - 1) = Some (bv_unsigned b)).
{ assert (Hl : (pred j < length (vr3_bytes U j))%nat) by (rewrite vr3_bytes_len by lia; lia).
  pose proof (HBy (pred j) Hl) as H0. rewrite vr3_bytes_nth in H0 by lia.
  replace ((pred j <? j)%nat) with true in H0 by (symmetry; apply Nat.ltb_lt; lia).
  rewrite <- Hb in H0. replace (q + Z.of_nat (pred j)) with (q + Z.of_nat j - 1) in H0 by lia. exact H0. }
assert (E11 : ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 11 = w64 (q + Z.of_nat j))
  by (rewrite (ew_Eimg_Ereg_nat regs _ 11 (Z_to_bv 5 11) eq_refl); exact R11).
assert (E19 : ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 19 = w64 SHADOW_OFF)
  by (rewrite (ew_Eimg_Ereg_nat regs _ 19 (Z_to_bv 5 19) eq_refl), (HK 19 ltac:(cbn; tauto)); exact H19).
assert (E18 : ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 18 = w64 q)
  by (rewrite (ew_Eimg_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl), (HK 18 ltac:(cbn; tauto)); exact H18).
assert (E32 : ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 32 = w64 (bv_unsigned b))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [w64 (bv_unsigned b)] 0)).
assert (E11u : bv_unsigned (ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 11) = q + Z.of_nat j)
  by (rewrite E11; unfold w64; apply unsigned_lit_small; lia).
assert (E19u : bv_unsigned (ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 19) = SHADOW_OFF)
  by (rewrite E19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32u : bv_unsigned (ew (Eimg (Ereg regs [w64 (bv_unsigned b)])) 32) = bv_unsigned b)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
exists (Eimg (Ereg regs [w64 (bv_unsigned b)])).
split; [apply Eimg_env|].
split; [split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]|].
split; [exact E11|]. split; [exact E19|]. split; [exact E18|]. split; [exact E32|].
split.
- rewrite restrict_mkst_fx. unfold vr3_ss. apply pa_entry_st_ok_full.
  + unfold vr3_regs.
    apply regs_ok_pin; [| vr3_bvne | cbn [sv_denot]; exact R14].
    apply regs_ok_pin; [| vr3_bvne | cbn [sv_denot]; exact R13].
    apply regs_ok_pin; [| vr3_bvne | cbn [sv_denot]; exact R12].
    apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | vr3_bvne |].
    cbn [sv_denot]. rewrite E11, R10. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vr3_rgn.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E11u.
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hqpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (q + Z.of_nat j) (-1) 1 (SOff 32 0) (bv_unsigned b)).
      -- cbn [sv_denot]. rewrite E32u, Z.add_0_r. reflexivity.
      -- replace (2 ^ (8 * Z.of_N 1)) with 256 by reflexivity. lia.
      -- lia.
      -- change (N.to_nat 1) with 1%nat. replace (q + Z.of_nat j + -1) with (q + Z.of_nat j - 1) by lia.
         apply vr3_val1_of_rd. exact Hby.
  + cbn. tauto.
  + unfold vr3_G. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E19u, E11u, E32u.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
- constructor; [|constructor].
  apply (shent_app_of_block SEGS B LAWS lyc Sc W mem md _ vr3_Bx 11 (q + Z.of_nat j) q (Z.of_nat (length U) + 1)
    (-1) 0 _ HAR HIN).
  + unfold vr3_Bx. apply (U_atom _ 19 SHADOW_OFF E19). unfold SHADOW_OFF; lia.
  + apply (U_atom _ 11 _ E11). lia.
  + lia.
  + lia.
  + rewrite vr3_req. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   One pass of the loop, from the loop head to the exit or back to the loop head *)
Lemma vr3_iter : forall j regs mem md, vr3_inv j regs mem md ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 27364)) mem (seg_rom SEGS)) md)
(fun W' c' => vr3_Q W' c' \/ (W' = W /\ exists regs' mem' md',
  c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 27364)) mem' (seg_rom SEGS)) md' /\ vr3_inv (pred j) regs' mem' md')).
Proof.
intros j regs mem md HI.
destruct (vr3_seed j regs mem md HI) as (E & HEI & HAE & E11 & E19 & E18 & E32 & HS & SHOK).
destruct HI as (Hj & R10 & R11 & R12 & R13 & R14 & HK & HJ & HF0 & HBy & HT).
remember (nth (pred j) U (Z_to_bv 8 0)) as b eqn:Hb.
pose proof (bv_unsigned_in_range 8 b) as Hv. change (bv_modulus 8) with 256 in Hv.
destruct (vr3_blk mem md (proj1 HJ)) as (Hq4 & Hqc & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hq64 : q + Z.of_nat (length U) + 1 < 2 ^ 64) by lia.
(* 0x8d014-0x8d02c: the trap branch `beq a1,a2` (not taken: atom 11 >= 4097), the check of the byte's shadow, the
   load; stuck at `bltu a3,a6` *)
paj_run_tok RUN HS HJ SHOK vr3_Bspan.
{ cbn [ms_mem mkst].
  rewrite (U_atom_off E 11 (q + Z.of_nat j) (-1) E11) by lia.
  apply (obl_of_block SEGS B LAWS lyc Sc W mem md E vr3_Bx _ 1 q (Z.of_nat (length U) + 1) (proj1 HJ) HIN);
    [unfold vr3_Bx; apply (U_atom E 19 SHADOW_OFF E19); unfold SHADOW_OFF; lia | lia | rewrite vr3_req; lia]. }
{ eapply (vr3_awr j E); [lia | lia | lia | reflexivity | exact E11]. }
vr3_md md1. vr3_ms HS ms1. cbn [ms_mem mkst] in HFr.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms1) a = rdW W mem a)
  by vr3_Kp HFr E11.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK vr3_Bspan.
- (* 32 < byte: not a trailing blank; 0x8d030 jumps to the exit *)
  rewrite branch_ltu_U, U_lit, (U_atom _ 32 (bv_unsigned b)) in Hc by first [vr3_ew E32 | lia].
  apply Z.ltb_lt in Hc.
  assert (Tb : PV.is_trail b = false) by (apply PVT.trail_gt; lia).
  paj_run_to_tok RUNTO HS HJ SHOK vr3_Bspan 27456.
  { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
  vr3_md md2. vr3_ms HS ms2.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a)
    by vr3_Kp HFr E11.
  clear HF HFr HG.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms2) a = rdW W mem a)
    by (intros a Ha Hne; rewrite K2, K1 by assumption; reflexivity).
  assert (BY : rdW W (ms_mem ms2) (q + Z.of_nat j - 1) = Some (bv_unsigned b)).
  { eapply (vr3_byte_at W _ _ ms2 _ (SOff 32 0) (q + Z.of_nat j) (bv_unsigned b) HS);
      [reflexivity | apply in_eq | vr3_ew E11 | lia | apply (U_atom _ 32); [vr3_ew E32 | lia] | lia]. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
    assert (HAEx : env_agree 32 (Ereg regs [w64 (bv_unsigned b)]) Ex) by env_agree_chain HAE;
    pose proof (vr3_kept_of Ex ssx (restrict (w_H W) ms2) regs [w64 (bv_unsigned b)] vr3_keepz HS HAEx
      ltac:(vm_compute; reflexivity)) as KR
  end.
  cbn [ms_regs restrict] in KR.
  pmkst HS. apply SRr_ret. left. split; [reflexivity|].
  exists (ms_regs ms2), (ms_mem ms2), md2. split; [reflexivity|].
  apply (vr3_out_of j); [lia | exact (vr3_kept_step regs _ HK KR) | exact HJ
    | exact (vr3_frame_step j mem _ ltac:(lia) HF0 KM)
    | apply (vr3_keep_bytes j mem); [lia | exact HBy | lia | lia | exact KM | rewrite <- Hb; exact BY]
    | apply (vr3_trim_keep j); [lia | exact HT | rewrite <- Hb; exact Tb]].
- (* byte <= 32: 0x8d034-0x8d038 compute (0x100002600 >> byte) & 1; stuck at `beqz a6` *)
  rewrite branch_ltu_U, U_lit, (U_atom _ 32 (bv_unsigned b)) in Hc by first [vr3_ew E32 | lia].
  apply Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK vr3_Bspan.
  { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
  vr3_md md2. vr3_ms HS ms2.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a)
    by vr3_Kp HFr E11.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK vr3_Bspan.
  + (* not a trailing blank: 0x8d03c jumps to the exit *)
    rewrite branch_eq_U, (vr3_bit _ (bv_unsigned b)), U_lit in Hc0 by first [vr3_ew E32 | lia].
    rewrite (PVT.trail_bit b) in Hc0 by lia.
    destruct (PV.is_trail b) eqn:Tb; cbn in Hc0; [discriminate Hc0|].
    paj_run_to_tok RUNTO HS HJ SHOK vr3_Bspan 27456.
    { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
    vr3_md md3. vr3_ms HS ms3.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms3) a = rdW W (ms_mem ms2) a)
      by vr3_Kp HFr E11.
    clear HF HFr HG.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms3) a = rdW W mem a)
      by (intros a Ha Hne; rewrite K3, K2, K1 by assumption; reflexivity).
    assert (BY : rdW W (ms_mem ms3) (q + Z.of_nat j - 1) = Some (bv_unsigned b)).
    { eapply (vr3_byte_at W _ _ ms3 _ (SOff 32 0) (q + Z.of_nat j) (bv_unsigned b) HS);
        [reflexivity | apply in_eq | vr3_ew E11 | lia | apply (U_atom _ 32); [vr3_ew E32 | lia] | lia]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
      assert (HAEx : env_agree 32 (Ereg regs [w64 (bv_unsigned b)]) Ex) by env_agree_chain HAE;
      pose proof (vr3_kept_of Ex ssx (restrict (w_H W) ms3) regs [w64 (bv_unsigned b)] vr3_keepz HS HAEx
        ltac:(vm_compute; reflexivity)) as KR
    end.
    cbn [ms_regs restrict] in KR.
    pmkst HS. apply SRr_ret. left. split; [reflexivity|].
    exists (ms_regs ms3), (ms_mem ms3), md3. split; [reflexivity|].
    apply (vr3_out_of j); [lia | exact (vr3_kept_step regs _ HK KR) | exact HJ
      | exact (vr3_frame_step j mem _ ltac:(lia) HF0 KM)
      | apply (vr3_keep_bytes j mem); [lia | exact HBy | lia | lia | exact KM | rewrite <- Hb; exact BY]
      | apply (vr3_trim_keep j); [lia | exact HT | rewrite <- Hb; exact Tb]].
  + (* a trailing blank: 0x8d040-0x8d04c check the store's shadow, write 0, a0 -= 1; stuck at `bltu s2,a1` *)
    rewrite branch_eq_U, (vr3_bit _ (bv_unsigned b)), U_lit in Hc0 by first [vr3_ew E32 | lia].
    rewrite (PVT.trail_bit b) in Hc0 by lia.
    destruct (PV.is_trail b) eqn:Tb; cbn in Hc0; [|discriminate Hc0].
    paj_run_tok RUN HS HJ SHOK vr3_Bspan.
    { rewrite (U_atom_off _ 11 (q + Z.of_nat j) (-1)) by first [vr3_ew E11 | lia].
      apply (obl_of_block SEGS B LAWS lyc Sc W _ _ _ vr3_Bx _ 1 q (Z.of_nat (length U) + 1) (proj1 HJ) HIN);
        [unfold vr3_Bx; apply (U_atom _ 19 SHADOW_OFF); [vr3_ew E19 | unfold SHADOW_OFF; lia]
        | lia | rewrite vr3_req; lia]. }
    { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
    vr3_md md3. vr3_ms HS ms3.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms3) a = rdW W (ms_mem ms2) a)
      by vr3_Kp HFr E11.
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK vr3_Bspan.
    * (* q < q + j - 1: back to the loop head *)
      rewrite branch_ltu_U, (U_atom _ 18 q), (U_atom_off _ 11 (q + Z.of_nat j) (-1)) in Hc1
        by first [vr3_ew E18 | vr3_ew E11 | lia].
      apply Z.ltb_lt in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK vr3_Bspan 27364.
      { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
      vr3_md md4. vr3_ms HS ms4.
      assert (K4 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms4) a = rdW W (ms_mem ms3) a)
        by vr3_Kp HFr E11.
      clear HF HFr HG.
      assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms4) a = rdW W mem a)
        by (intros a Ha Hne; rewrite K4, K3, K2, K1 by assumption; reflexivity).
      assert (BY0 : rdW W (ms_mem ms4) (q + Z.of_nat j - 1) = Some 0).
      { eapply (vr3_byte_at W _ _ ms4 _ (SLit 0) (q + Z.of_nat j) 0 HS);
          [reflexivity | apply in_eq | vr3_ew E11 | lia | apply U_lit; lia | lia]. }
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        assert (HAEx : env_agree 32 (Ereg regs [w64 (bv_unsigned b)]) Ex) by env_agree_chain HAE;
        pose proof (vr3_kept_of Ex ssx (restrict (w_H W) ms4) regs [w64 (bv_unsigned b)] vr3_keepz HS HAEx
          ltac:(vm_compute; reflexivity)) as KR
      end.
      cbn [ms_regs restrict] in KR.
      prreg HS (Z_to_bv 5 10) N10. prreg HS (Z_to_bv 5 11) N11. prreg HS (Z_to_bv 5 12) N12.
      prreg HS (Z_to_bv 5 13) N13. prreg HS (Z_to_bv 5 14) N14.
      destruct (vr3_store_bytes j mem (ms_mem ms4)) as (HBy' & HT');
        [lia | exact HBy | exact HT | rewrite <- Hb; exact Tb | lia | lia | exact KM | exact BY0 |].
      pmkst HS. apply SRr_ret. right. split; [reflexivity|].
      exists (ms_regs ms4), (ms_mem ms4), md4. split; [reflexivity|].
      split; [lia|].
      split; [rewrite N10, E11; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
      split; [rewrite N11, E11; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
      split; [exact N12|]. split; [exact N13|]. split; [exact N14|].
      split; [exact (vr3_kept_step regs _ HK KR)|].
      split; [exact HJ|].
      split; [exact (vr3_frame_step j mem _ ltac:(lia) HF0 KM)|].
      split; [exact HBy' | exact HT'].
    * (* j = 1: the line was all blanks; 0x8d054 jumps to the exit *)
      rewrite branch_ltu_U, (U_atom _ 18 q), (U_atom_off _ 11 (q + Z.of_nat j) (-1)) in Hc1
        by first [vr3_ew E18 | vr3_ew E11 | lia].
      apply Z.ltb_ge in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK vr3_Bspan 27456.
      { eapply (vr3_awr j); [lia | lia | lia | reflexivity | vr3_ew E11]. }
      vr3_md md4. vr3_ms HS ms4.
      assert (K4 : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms4) a = rdW W (ms_mem ms3) a)
        by vr3_Kp HFr E11.
      clear HF HFr HG.
      assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> q + Z.of_nat j - 1 -> rdW W (ms_mem ms4) a = rdW W mem a)
        by (intros a Ha Hne; rewrite K4, K3, K2, K1 by assumption; reflexivity).
      assert (BY0 : rdW W (ms_mem ms4) (q + Z.of_nat j - 1) = Some 0).
      { eapply (vr3_byte_at W _ _ ms4 _ (SLit 0) (q + Z.of_nat j) 0 HS);
          [reflexivity | apply in_eq | vr3_ew E11 | lia | apply U_lit; lia | lia]. }
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
        assert (HAEx : env_agree 32 (Ereg regs [w64 (bv_unsigned b)]) Ex) by env_agree_chain HAE;
        pose proof (vr3_kept_of Ex ssx (restrict (w_H W) ms4) regs [w64 (bv_unsigned b)] vr3_keepz HS HAEx
          ltac:(vm_compute; reflexivity)) as KR
      end.
      cbn [ms_regs restrict] in KR.
      destruct (vr3_store_bytes j mem (ms_mem ms4)) as (HBy' & HT');
        [lia | exact HBy | exact HT | rewrite <- Hb; exact Tb | lia | lia | exact KM | exact BY0 |].
      pmkst HS. apply SRr_ret. left. split; [reflexivity|].
      exists (ms_regs ms4), (ms_mem ms4), md4. split; [reflexivity|].
      apply (vr3_out_of (pred j)); [lia | exact (vr3_kept_step regs _ HK KR) | exact HJ
        | exact (vr3_frame_step j mem _ ltac:(lia) HF0 KM) | exact HBy' |].
      rewrite HT'. replace (pred j) with 0%nat by lia. reflexivity.
Qed.

Lemma vr3_loop : forall j regs mem md, vr3_inv j regs mem md ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 27364)) mem (seg_rom SEGS)) md) vr3_Q.
Proof.
induction j as [|j IH]; intros regs mem md HI.
- exfalso. destruct HI as (Hj & _). lia.
- eapply SRr_bind; [exact (vr3_iter (Datatypes.S j) regs mem md HI)|].
  cbv beta. intros W' c' _ [HQ | (-> & regs' & mem' & md' & -> & HI')].
  + apply SRr_ret. exact HQ.
  + apply (IH regs' mem' md'). exact HI'.
Qed.

End loop.
End e.
End f.
End d.
