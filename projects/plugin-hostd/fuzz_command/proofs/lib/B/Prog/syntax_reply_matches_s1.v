(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the leaf walk) and
   lib/A/AC8b.v (a loop by fuel induction) at c8557374ad2e: the walk of syntax_reply_matches on fuzz_command.asan.
   This file: the walk's state (the entry facts, the invariant every segment carries, the post-condition) and the
   epilogue segment. *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/syntax_reply_matches_s1.v (a working branch
   db7d4effe38) for fuzz_command.asan-ubsan: module paths, the B program points, the constants the B prologue loads
   (s7 = -1, s8 = the shadow base, s9 = 60, s10 = 90, s1 = 93; a6 = 91 is caller-saved and is carried with a5),
   the strcspn set .str.5 at 0x21160, the stack-protector cells 0xa6bf8 / 0x604158, and the tail's UBSan null check. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import syntax_reply_matches_c PaNoChain.
(* the plain proof's pure lemmas over the model (lib/Prog/syntax_reply_matches.v:10-241), used as they are *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require syntax_reply_matches.
Module PSRM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.syntax_reply_matches.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require CommandTac.
Module PCT := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.CommandTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* Program points, as offsets of the listing (BASE = 0x86530, the function at AF_syntax_reply_matches = 0x2368):
   ENTRY 0x88898, L0 0x8890c (the item loop), L1 0x88918 (skip ' '), L2 0x8895c (scan one item), CALL1 0x889c8
   (strcspn), RET1 0x889d4, L3 0x889ec (look for '<'), NOLT 0x88a2c (bcmp), RET2 0x88a3c, JOIN 0x88a40,
   JOIN2 0x88a98, TAIL 0x88ac0, EPI 0x88adc. Every UBSan trap branch goes to the `unimp` at 0x88b20. *)

Definition SRM_L0 : Z := 0x23dc.
Definition SRM_L1 : Z := 0x23e8.
Definition SRM_L2 : Z := 0x242c.
Definition SRM_CALL1 : Z := 0x2498.
Definition SRM_RET1 : Z := 0x24a4.
Definition SRM_L3 : Z := 0x24bc.
Definition SRM_NOLT : Z := 0x24fc.
Definition SRM_RET2 : Z := 0x250c.
Definition SRM_JOIN : Z := 0x2510.
Definition SRM_JOIN2 : Z := 0x2568.
Definition SRM_TAIL : Z := 0x2590.
Definition SRM_EPI : Z := 0x25ac.
(* the 13 saved registers and their slots above the new stack pointer (dis:3-15) *)
Definition SRM_SAVES : list (bv 5 * Z) :=
  [(1%bv, 104); (8%bv, 96); (9%bv, 88); (18%bv, 80); (19%bv, 72); (20%bv, 64); (21%bv, 56); (22%bv, 48);
   (23%bv, 40); (24%bv, 32); (25%bv, 24); (26%bv, 16); (27%bv, 8)].
Definition srm_byte (l : list byte) (i : nat) : Z := bv_unsigned (nth i l (Z_to_bv 8 0)).
Lemma srm_byte_range : forall l i, 0 <= srm_byte l i < 256.
Proof. intros l i. unfold srm_byte. pose proof (bv_unsigned_in_range 8 (nth i l (Z_to_bv 8 0))) as H. exact H. Qed.
Lemma hd_skipn_nth : forall (l : list byte) i d, hd d (skipn i l) = nth i l d.
Proof. induction l as [|x l IH]; intros [|i] d; cbn; try reflexivity. apply IH. Qed.
Lemma srm_byte_app_lt : forall (l : list byte) i, (i < length l)%nat -> srm_byte (l ++ [Z_to_bv 8 0]) i = srm_byte l i.
Proof. intros l i Hi. unfold srm_byte. rewrite app_nth1 by exact Hi. reflexivity. Qed.
Lemma srm_byte_app_end : forall (l : list byte), srm_byte (l ++ [Z_to_bv 8 0]) (length l) = 0.
Proof. intros l. unfold srm_byte. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation STK := SYNTAX_REPLY_MATCHES_STK.

(* The entry state of the walk and the facts the walk uses of it. The statement's premises give them
   (syntax_reply_matches.v, the top theorem); the walk lemmas are stated over this record. *)
Record srm_ctx := mkSRM {
  x_ly : alayout; x_S : astate; x_W : world SEGS; x_regs : bvmap 5 word; x_mem : word -> option byte;
  x_md : Model; x_P : Z; x_R : Z; x_shape : list byte; x_reply : list byte }.

Section e.
Variable B : asyms.
Definition srm_sp0 (x : srm_ctx) : Z := spZ (x_regs x).
Definition srm_ok (x : srm_ctx) : Prop :=
  let W := x_W x in let m0 := x_mem x in let P := x_P x in let R := x_R x in
  let ns := Z.of_nat (length (x_shape x)) in let nr := Z.of_nat (length (x_reply x)) in
  afn_pre_na SEGS B STK (x_ly x) (x_S x) W (x_regs x) m0 (x_md x) /\
  getr (x_regs x) 10 = w64 P /\ getr (x_regs x) 11 = w64 R /\
  (* the shape: a NUL-terminated string below the allocator ceiling, addressable, with its shadow words visible *)
  astr_atR (rdW W m0) P (x_shape x) /\ 4096 <= P /\ P + ns + 1 <= alloc_ceiling /\ amem_range P (ns + 1) /\
  range_addressable (rdW W m0) SHADOW_OFF P (ns + 1) /\ shadow_hull_vis (rdW W m0) P (ns + 1) /\ ns < 2 ^ 31 /\
  (* the reply: the same, plus the bytes to the end of its terminator's 8-byte word; its band room reaches 8 bytes past
     the reply (the strcspn entry's `+ 8` premise, RtString.v:166) *)
  astr_atR (rdW W m0) R (x_reply x) /\ 4096 <= R /\ R + nr + 1 <= alloc_ceiling /\ amem_range R (nr + 8) /\
  range_addressable (rdW W m0) SHADOW_OFF R (nr + 1) /\ shadow_hull_vis (rdW W m0) R (nr + 1) /\ nr < 2 ^ 28 /\
  atail_vis SEGS W m0 (R + nr) /\
  (* the set " " (.str.5) and the stack-protector cells the strcspn entry reads *)
  cmd_ro_ok (rdW W m0) /\ cmd_val_objs /\ aguard_ok SEGS W m0 0xa6bf8 0x604158 /\
  range_addressable (rdW W m0) SHADOW_OFF 0x21160 2 /\ shadow_hull_vis (rdW W m0) 0x21160 2 /\
  atail_vis SEGS W m0 0x21161 /\
  (* the unowned ROM bytes, as the strcspn entry asks them (a Theorem Labs lane's rt_rom_view, the premise of astrcspn_realizes) *)
  rt_rom_view SEGS B W m0.

Definition srm_post (x : srm_ctx) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK [] (x_regs x) (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) EV_SYNTAX_REPLY_MATCHES
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (if reply_matches (x_shape x) (x_reply x) then 1 else 0) /\
       Permutation (ablocks B ly' S') (ablocks B (x_ly x) (x_S x)) /\
       ly' = x_ly x /\ S' = x_S x).

Definition srm_frame (x : srm_ctx) (m : word -> option byte) : Prop :=
  Forall (fun ro => val_mem SEGS (mrestrict (w_H (x_W x)) m) (srm_sp0 x - 112 + snd ro) 8
                      (bv_unsigned (getr (x_regs x) (fst ro)))) SRM_SAVES.

(* What every segment carries: the journal from the entry, all memory outside the stack window unchanged, the 13
   saved registers in the frame, the stack pointer, gp and tp, and the callee-saved constants the prologue loads
   (s8 = the shadow base, s6 = ' ', s9 = '<', s10 = 'Z', s1 = ']', s7 = -1, the operand of the UBSan checks). *)
Definition srm_inv (x : srm_ctx) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B STK (srm_sp0 x) [] (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) [] (x_ly x) (x_S x) (x_W x) m md 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (srm_sp0 x - STK <= a < srm_sp0 x) -> rdW (x_W x) m a = rdW (x_W x) (x_mem x) a) /\
  srm_frame x m /\
  getr regs 2 = w64 (srm_sp0 x - 112) /\ getr regs 3 = getr (x_regs x) 3 /\ getr regs 4 = getr (x_regs x) 4 /\
  getr regs 24 = w64 SB /\ getr regs 22 = w64 32 /\ getr regs 25 = w64 60 /\ getr regs 26 = w64 90 /\
  getr regs 9 = w64 93 /\ getr regs 23 = w64 (2 ^ 64 - 1).

Definition srm_at (x : srm_ctx) (pc : Z) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  SRr SEGS (x_W x) (mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)) md) (srm_post x).

Lemma srm_ok_facts : forall x, srm_ok x ->
  let ns := Z.of_nat (length (x_shape x)) in let nr := Z.of_nat (length (x_reply x)) in
  alloc_ceiling <= ly_stk_lo (x_ly x) /\ ly_stk_lo (x_ly x) + STK <= srm_sp0 x /\ srm_sp0 x <= 2 ^ 47 /\
  srm_sp0 x mod 16 = 0 /\
  4096 <= x_P x /\ x_P x + ns + 1 <= alloc_ceiling /\ 4096 <= x_R x /\ x_R x + nr + 1 <= alloc_ceiling /\
  ns < 2 ^ 31 /\ nr < 2 ^ 28.
Proof.
intros x HX ns nr. pose proof HX as (HPRE & _ & _ & _ & HP1 & HP2 & _ & _ & _ & HL & _ & HR1 & HR2 & _ & _ & _ & HL2 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
unfold srm_sp0. repeat split; lia.
Qed.

(* memory facts carried by srm_inv *)
Lemma srm_rd_kept : forall x regs m md a, srm_ok x -> srm_inv x regs m md -> 0 <= a < alloc_ceiling ->
  rdW (x_W x) m a = rdW (x_W x) (x_mem x) a.
Proof.
intros x regs m md a HX (_ & KEEP & _) Ha. pose proof (srm_ok_facts x HX) as (F1 & F2 & _).
pose proof asan_consts as (C1 & _). apply KEEP; [lia|]. unfold STK, SYNTAX_REPLY_MATCHES_STK, ESTACK in *. lia.
Qed.
Lemma srm_shape_byte : forall x regs m md i, srm_ok x -> srm_inv x regs m md -> (i <= length (x_shape x))%nat ->
  rdW (x_W x) m (x_P x + Z.of_nat i) = Some (srm_byte (x_shape x ++ [Z_to_bv 8 0]) i).
Proof.
intros x regs m md i HX HI Hi. pose proof (srm_ok_facts x HX) as (_ & _ & _ & _ & HP1 & HP2 & _).
pose proof HX as (_ & _ & _ & [HS _] & _).
rewrite (srm_rd_kept x regs m md _ HX HI) by lia. apply HS. rewrite length_app. cbn [length]. lia.
Qed.
Lemma srm_reply_byte : forall x regs m md i, srm_ok x -> srm_inv x regs m md -> (i <= length (x_reply x))%nat ->
  rdW (x_W x) m (x_R x + Z.of_nat i) = Some (srm_byte (x_reply x ++ [Z_to_bv 8 0]) i).
Proof.
intros x regs m md i HX HI Hi. pose proof (srm_ok_facts x HX) as (_ & _ & _ & _ & _ & _ & HR1 & HR2 & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [HS _] & _).
rewrite (srm_rd_kept x regs m md _ HX HI) by lia. apply HS. rewrite length_app. cbn [length]. lia.
Qed.
(* the shadow facts at the current state: the shadow of an address below the ceiling is below the stack *)
Lemma srm_ra_kept : forall x regs m md a n, srm_ok x -> srm_inv x regs m md -> 0 <= a -> a + n <= alloc_ceiling ->
  range_addressable (rdW (x_W x) (x_mem x)) SHADOW_OFF a n -> range_addressable (rdW (x_W x) m) SHADOW_OFF a n.
Proof.
intros x regs m md a n HX HI Ha Hn H y Hy. destruct (H y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite (srm_rd_kept x regs m md _ HX HI); [exact Hs|]. pose proof asan_consts as (C1 & _). unfold shadow_of_addr, SHADOW_OFF in *.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma srm_hull_kept : forall x regs m md a n, srm_ok x -> srm_inv x regs m md -> 0 <= a -> a + n <= alloc_ceiling -> 0 < n ->
  shadow_hull_vis (rdW (x_W x) (x_mem x)) a n -> shadow_hull_vis (rdW (x_W x) m) a n.
Proof.
intros x regs m md a n HX HI Ha Hn Hn0 H y Hy. rewrite (srm_rd_kept x regs m md _ HX HI); [exact (H y Hy)|].
pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (0x7fff8000 + a / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (0x7fff8000 + a / 8) 8 ltac:(lia)).
pose proof (Z.div_le_upper_bound (0x7fff8000 + (a + n - 1) / 8) 8 (2 ^ 42) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma ew_EI_w64 : forall regs extra n (r : bv 5) v, (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg regs extra)) n) = v.
Proof.
intros regs extra n r v Hn Hr H Hv. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs extra n r Hr), H.
unfold w64. apply unsigned_lit_small. exact Hv.
Qed.
Lemma ew_EX_w64 : forall regs extra j v, (32 + j < 240)%nat -> nth j extra (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (Ereg regs extra)) (32 + j)) = v.
Proof.
intros regs extra j v Hj H Hv. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, H.
unfold w64. apply unsigned_lit_small. exact Hv.
Qed.
Lemma ra_agree_all : forall (rd rd' : Z -> option Z) a n, (forall y, 0 <= y < 2 ^ 64 -> rd' y = rd y) -> 0 <= a ->
  a + n <= 2 ^ 60 -> range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n H Ha Hn H2. apply (range_addressable_agree rd rd'); [|exact H2]. intros y Hy. apply H.
unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound y 8 (2 ^ 57) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma shadow_hull_vis_sub : forall rd a n a' n', shadow_hull_vis rd a n -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1). pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma le_byte_1_0 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
intros z Hz. unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small z (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia.
Qed.
Lemma val_mem1_of_aview : forall (H : word -> bool) m a v, aview SEGS H m a = Some v ->
  val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. replace (a + Z.of_nat 0) with a by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate]. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite le_byte_1_0 by lia. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the frame slots are kept when memory outside a window below the new stack pointer is kept *)
Lemma srm_frame_kept : forall x m m', srm_frame x m ->
  (forall a, srm_sp0 x - 112 <= a < srm_sp0 x -> rdW (x_W x) m' a = rdW (x_W x) m a) -> srm_frame x m'.
Proof.
intros x m m' HF HK. unfold srm_frame in *. apply Forall_forall. intros ro Hro.
pose proof (proj1 (Forall_forall _ _) HF ro Hro) as Hv.
assert (Hoff : 8 <= snd ro <= 104) by (cbv [SRM_SAVES In] in Hro; repeat (destruct Hro as [<-|Hro]; [cbn; lia|]); destruct Hro).
intros k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview SEGS). apply HK. lia.
Qed.

Lemma aregs_preserved_of_list : forall regs regs',
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
   getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> aregs_preserved regs regs'.
Proof. intros regs regs' H r Hr. apply H. unfold acallee_saved in Hr. cbn [In]. lia. Qed.

Lemma w64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

(* ---- The epilogue (EPI, 0x88adc): restore the 13 registers, pop the frame, return. ---- *)
Definition epi_chunks : list YP09.chunk :=
  [YP09.mkChunk 104 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 34 0));
   YP09.mkChunk 80 (CVal 8 (SOff 35 0)); YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 37 0));
   YP09.mkChunk 56 (CVal 8 (SOff 38 0)); YP09.mkChunk 48 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 8 (SOff 40 0));
   YP09.mkChunk 32 (CVal 8 (SOff 41 0)); YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 16 (CVal 8 (SOff 43 0));
   YP09.mkChunk 8 (CVal 8 (SOff 44 0))].
Definition epi_region : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0 epi_chunks.
Definition ss_epi : sstate := mkSS (AF_syntax_reply_matches + 0x244) sr_atoms [epi_region] None (mkFacts [] [] []).
Definition epi_extra (x : srm_ctx) : list word := map (fun ro => getr (x_regs x) (fst ro)) SRM_SAVES.
Definition SRM_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition SRM_Bx : sv := SOff 24 0.

Definition CEIL_HI : Z := 0x7fffff800000.
Fixpoint srm_pins (sr : list sv) (l : list (bv 5 * sv)) : list sv :=
  match l with [] => sr | p :: l' => srm_pins (sr_set sr (fst p) (snd p)) l' end.
Lemma regs_ok_pins : forall E l sr regs, regs_ok E sr regs ->
  Forall (fun p => fst p <> 0%bv /\ getr regs (fst p) = sv_denot E (snd p)) l -> regs_ok E (srm_pins sr l) regs.
Proof.
intros E l. induction l as [|p l IH]; intros sr regs H HF; cbn [srm_pins]; [exact H|].
inversion HF as [|? ? [H0 H1] HF']; subst. apply IH; [|exact HF']. apply regs_ok_pin; assumption.
Qed.
Lemma srm_seed : forall (W : world SEGS) regs m pc l rs fs cs al extra,
  Forall (fun p => fst p <> 0%bv /\ getr regs (fst p) = sv_denot (Eimg (Ereg regs extra)) (snd p)) l ->
  regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs extra)) (mrestrict (w_H W) m)) rs ->
  pairwise_disjoint (Eimg (Ereg regs extra)) rs ->
  facts_ok (Eimg (Ereg regs extra)) (mkFacts fs cs al) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc (srm_pins sr_atoms l) rs None (mkFacts fs cs al))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros W regs m pc l rs fs cs al extra Hl Hwf Hrs Hpd HG. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; try assumption. apply regs_ok_pins; [apply regs_ok_Eimg_Ereg | exact Hl].
Qed.
Lemma frame_ro_keep : forall E rs H m m', frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a Ha. apply (kept_of_frame (segs:=SEGS) E rs H m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Hr. unfold windows in Hin. apply in_map_iff in Hin as (r & Hr' & Hin).
pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw.
injection Hr' as <- <- <-. lia.
Qed.
Lemma ew_EI : forall regs extra n, (n < 32)%nat -> ew (Eimg (Ereg regs extra)) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof. intros regs extra n Hn. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_lt. exact Hn. Qed.
Lemma ew_EX : forall regs extra j, (32 + j < 240)%nat -> ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma sv_w64 : forall E v z, U E v = z -> sv_denot E v = w64 z.
Proof. intros E v z H. subst z. unfold w64, U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition SRM_KEEP : list (bv 5) := [2; 3; 4; 9; 22; 23; 24; 25; 26]%bv.
Lemma srm_inv_next : forall x regs m md regs' m' md', srm_ok x -> srm_inv x regs m md ->
  ajournal SEGS B STK (srm_sp0 x) [] (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) [] (x_ly x) (x_S x) (x_W x) m' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) m' a = rdW (x_W x) m a) ->
  (forall r, In r SRM_KEEP -> getr regs' r = getr regs r) ->
  srm_inv x regs' m' md'.
Proof.
intros x regs m md regs' m' md' HX (HJ & KEEP & HFR & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23) HJ' HM HR.
pose proof (srm_ok_facts x HX) as (F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
split; [exact HJ'|]. split.
{ intros a Ha Hn. rewrite (HM a Ha). exact (KEEP a Ha Hn). }
split.
{ apply (srm_frame_kept x m m' HFR). intros a Ha. apply HM. unfold STK, SYNTAX_REPLY_MATCHES_STK, ESTACK in *. lia. }
unfold SRM_KEEP in HR.
rewrite (HR 2%bv), (HR 3%bv), (HR 4%bv), (HR 24%bv), (HR 22%bv), (HR 25%bv), (HR 26%bv), (HR 9%bv), (HR 23%bv)
  by (cbn [In]; tauto).
repeat split; assumption.
Qed.
(* after a runtime entry called at sp0 - 112 with a scratch window of 2 * ESTACK below it *)
Lemma srm_inv_call : forall x regs m md regs' m' md', srm_ok x -> srm_inv x regs m md ->
  ajournal SEGS B STK (srm_sp0 x) [] (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) [] (x_ly x) (x_S x) (x_W x) m' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (srm_sp0 x - 112 - 2 * ESTACK <= a < srm_sp0 x - 112) -> rdW (x_W x) m' a = rdW (x_W x) m a) ->
  aregs_preserved regs regs' ->
  srm_inv x regs' m' md'.
Proof.
intros x regs m md regs' m' md' HX (HJ & KEEP & HFR & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23) HJ' HM HP.
pose proof (srm_ok_facts x HX) as (F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (HSTK : STK = 8304) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
split; [exact HJ'|]. split.
{ intros a Ha Hn. rewrite (HM a Ha) by lia. exact (KEEP a Ha Hn). }
split.
{ apply (srm_frame_kept x m m' HFR). intros a Ha. apply HM; lia. }
assert (Q2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Q3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (Q4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (Q9 : getr regs' 9%bv = getr regs 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (Q22 : getr regs' 22%bv = getr regs 22%bv) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
assert (Q23 : getr regs' 23%bv = getr regs 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (Q24 : getr regs' 24%bv = getr regs 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (Q25 : getr regs' 25%bv = getr regs 25%bv) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
assert (Q26 : getr regs' 26%bv = getr regs 26%bv) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
rewrite Q2, Q3, Q4, Q24, Q22, Q25, Q26, Q9, Q23.
repeat split; assumption.
Qed.
Lemma amem_range_sub : forall p n p' n', amem_range p n -> p <= p' -> p' + n' <= p + n -> amem_range p' n'.
Proof. intros p n p' n' H H1 H2. unfold amem_range in *. lia. Qed.
Lemma firstn_nth_eq : forall (l1 l2 : list byte) L, (L <= length l1)%nat -> (L <= length l2)%nat ->
  (forall i, (i < L)%nat -> nth i l1 (Z_to_bv 8 0) = nth i l2 (Z_to_bv 8 0)) -> firstn L l1 = firstn L l2.
Proof.
induction l1 as [|a l1 IH]; intros l2 L H1 H2 H; destruct L as [|L]; cbn in *; try reflexivity; try lia.
destruct l2 as [|c l2]; cbn in *; [lia|]. f_equal; [exact (H 0%nat ltac:(lia))|].
apply IH; [lia | lia|]. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.
Lemma nth_firstn_lt : forall (l : list byte) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
induction l as [|a l IH]; intros [|L] [|i] d H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.
Lemma nth_firstn_eq : forall (l1 l2 : list byte) L i, firstn L l1 = firstn L l2 -> (i < L)%nat ->
  nth i l1 (Z_to_bv 8 0) = nth i l2 (Z_to_bv 8 0).
Proof.
intros l1 l2 L i H Hi. rewrite <- (nth_firstn_lt l1 L i _ Hi), <- (nth_firstn_lt l2 L i _ Hi), H. reflexivity.
Qed.
Lemma srm_byte_le : forall l i, (i < length l)%nat -> ~ In (Z_to_bv 8 0) l -> srm_byte l i <> 0.
Proof.
intros l i Hi Hn H. apply Hn. unfold srm_byte in H. replace (Z_to_bv 8 0) with (nth i l (Z_to_bv 8 0)); [apply nth_In; exact Hi|].
apply bv_eq. rewrite H. reflexivity.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma srm_epi : forall x regs m md, srm_ok x -> srm_inv x regs m md ->
  getr regs 10 = w64 (if reply_matches (x_shape x) (x_reply x) then 1 else 0) ->
  srm_at x SRM_EPI regs m md.
Proof.
intros x regs m md HX HI H10. unfold srm_at.
pose proof pa_segs_low as Hsegs.
pose proof (srm_ok_facts x HX) as (F1 & F2 & F3 & F4 & _).
pose proof HX as (HPRE & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof HI as (HJ & KEEP & HFR & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
assert (HSTK : STK = 8304) by reflexivity.
remember (Eimg (Ereg regs (epi_extra x))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (epi_extra x)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (EX : forall n, (32 <= n < 45)%nat -> ew E n = getr (x_regs x) (fst (nth (n - 32) SRM_SAVES (0%bv, 0)))).
{ intros n Hn. rewrite EL by (unfold A_TEXT; lia). replace n with (32 + (n - 32))%nat at 1 by lia.
  rewrite ew_Ereg_extra. unfold epi_extra.
  rewrite (nth_indep _ _ (getr (x_regs x) (fst (0%bv, 0)))) by (rewrite length_map; cbn; lia).
  rewrite (map_nth (fun ro => getr (x_regs x) (fst ro))). reflexivity. }
pose proof asan_consts as (C1 & _).
assert (Usp : bv_unsigned (ew E 2) = srm_sp0 x - 112) by (rewrite E2, R2; apply w64_unsigned; lia).
assert (HS : st_ok_pi SEGS VAL E ss_epi (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_EPI)) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_epi, SRM_EPI.
  replace (AF_syntax_reply_matches + 0x244) with 0x25ac by reflexivity.
  apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, epi_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold srm_frame in HFR. unfold SRM_SAVES in HFR. unfold epi_chunks.
    repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H end.
    cbn [fst snd] in *.
    repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- context [YP09.mkChunk ?off (CVal _ (SOff ?n 0))] =>
      apply (chunk_ok_val SEGS E _ _ off 8 (SOff n 0) (bv_unsigned (getr (x_regs x) (fst (nth (n - 32) SRM_SAVES (0%bv, 0))))));
      [ cbn [sv_denot]; rewrite (EX n) by lia; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | apply bv_unsigned_in_range | lia
      | change (N.to_nat 8) with 8%nat; cbn [nth SRM_SAVES fst Nat.sub]; assumption ] end.
  - cbn. tauto.
  - split; [cbn; exact I | split; cbn; exact I]. }
clear HE EL.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
eapply (RET (x_W x) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold srm_post, apost_base.
eexists (x_ly x), (x_S x), _, _, _. split.
{ rewrite Q1, (EX 32%nat) by lia. cbn [nth SRM_SAVES fst Nat.sub]. rewrite Hra. reflexivity. }
split; [unfold EV_SYNTAX_REPLY_MATCHES; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split.
{ apply aregs_preserved_of_list. intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ lazymatch goal with |- getr (ms_regs ?msx) ?rr = _ =>
        let Q := fresh "Q" in prreg HS rr Q; rewrite Q end;
      first [ rewrite Usp; unfold srm_sp0, spZ; replace (bv_unsigned (getr (x_regs x) 2) - 112 + 112) with (bv_unsigned (getr (x_regs x) 2)) by lia;
              rewrite Z_to_bv_bv_unsigned; reflexivity
            | rewrite E3, R3; reflexivity
            | rewrite E4, R4; reflexivity
            | lazymatch goal with |- ew _ ?n = _ => rewrite (EX n) by lia; reflexivity end ]
    |]).
  destruct Hr. }
split; [rewrite Q10, E10; exact H10 | split; [apply Permutation_refl | split; reflexivity]].
Qed.
Lemma U_extK_atom : forall E K ws n v c, (n < K)%nat -> ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U (extK E K ws) (SOff n c) = v + c.
Proof. intros E K ws n v c Hn Hv Hr Hc. apply U_atom_off; [|lia|lia]. rewrite (proj1 (env_agree_extK E K ws) n Hn). exact Hv. Qed.
Lemma env_agree_after : forall regs extra E K ws, env_agree 32 (Ereg regs extra) E -> (32 <= K)%nat ->
  env_agree 32 (Ereg regs extra) (extK E K ws).
Proof.
intros regs extra E K ws H HK. eapply env_agree_trans; [exact H|]. eapply env_agree_le; [|apply env_agree_extK]. exact HK.
Qed.

(* ---- TAIL (0x88ac0): the UBSan null check of s0 = R + j (trap site 0x88ac0: R + j >= 4096 decides it), check C6 on
   s0, return *reply == '\0' ---- *)
Definition tail_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition tail_facts : list (nat * afact) := [(8%nat, mkAF 4096 CEIL_HI 0); (24%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)].
Lemma srm_tail : forall x regs m md j, srm_ok x -> srm_inv x regs m md -> (j <= length (x_reply x))%nat ->
  reply_matches_items [] (skipn j (x_reply x)) = reply_matches (x_shape x) (x_reply x) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> srm_at x SRM_TAIL regs m md.
Proof.
intros x regs m md j HX HI Hj HV H8. unfold srm_at.
pose proof (srm_ok_facts x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
set (b := srm_byte (x_reply x ++ [Z_to_bv 8 0]) j).
pose proof (srm_byte_range (x_reply x ++ [Z_to_bv 8 0]) j) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 b]) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8 : ew E 8 = w64 (x_R x + Z.of_nat j)) by (subst E; rewrite ew_EI by lia; exact H8).
assert (E24 : ew E 24 = w64 SB) by (subst E; rewrite ew_EI by lia; exact R24).
assert (E32 : ew E 32 = w64 b) by (subst E; apply (ew_EX regs [w64 b] 0); lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_TAIL (srm_pins sr_atoms []) [tail_region] None (mkFacts tail_facts [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_TAIL)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, tail_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8, w64_unsigned by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 32 0) b).
    + cbn [sv_denot]. rewrite E32, w64_unsigned by lia. rewrite Z.add_0_r. reflexivity.
    + simpl. lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      exact (srm_reply_byte x regs m md j HX HI Hj).
  - cbn. tauto.
  - unfold facts_ok, tail_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E8, E24, E32, !w64_unsigned by (unfold SB; lia). unfold CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_EPI.
all: first [ awr_ok_tac | lazymatch goal with |- range_addressable _ _ _ _ => idtac end | idtac ].
{ change (rd_of SEGS (mrestrict (w_H (x_W x)) m)) with (rdW (x_W x) m). unfold SRM_Bx.
  rewrite (U_atom E 24 SB E24) by (unfold SB; lia).
  rewrite (U_atom E 8 (x_R x + Z.of_nat j) E8) by lia.
  pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRA & _).
  eapply (range_addressable_sub _ _ (x_R x) (Z.of_nat (length (x_reply x)) + 1));
    [ eapply (srm_ra_kept x regs m md); [exact HX | exact HI | lia | lia | exact HRA] | lia | lia ]. }
assert (KM := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
assert (HK : forall r, In r SRM_KEEP -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. pose proof (regs_kept_of_st_ok_pi _ _ _ regs [w64 b] SRM_KEEP HS) as HKs.
  cbn [ms_regs restrict] in HKs. apply HKs; [env_agree_chain HAE | vm_compute; reflexivity | exact Hr]. }
pmkst HS.
eapply (srm_epi x (ms_regs ms) (ms_mem ms) _ HX).
- eapply srm_inv_next; [exact HX | exact HI | exact HJ | intros a Ha; exact (KM a Ha) | exact HK].
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS).
  lazymatch goal with |- sv_denot _ (sr_get ?sr _) = _ =>
    let e := eval vm_compute in (sr_get sr 10%bv) in change (sr_get sr 10%bv) with e end.
  apply sv_w64. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit. cbn [ew ewset Nat.eqb].
  rewrite E32, w64_unsigned by lia. rewrite Z.add_0_r. unfold zcanon, M64.
  rewrite (Z.mod_small b) by lia. rewrite (Z.mod_small 1) by lia.
  rewrite <- HV. pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ HRn] & _).
  destruct (Nat.lt_ge_cases j (length (x_reply x))) as [Lj|Lj].
  + assert (Hb0 : b <> 0) by (unfold b; rewrite srm_byte_app_lt by exact Lj; apply srm_byte_le; assumption).
    destruct (skipn j (x_reply x)) eqn:Es; [apply (f_equal (@length byte)) in Es; rewrite length_skipn in Es; cbn in Es; lia|].
    cbn [reply_matches_items]. rewrite (proj2 (Z.ltb_ge b 1)) by lia. reflexivity.
  + assert (j = length (x_reply x)) by lia. subst j.
    assert (Hb0 : b = 0) by (unfold b; apply srm_byte_app_end).
    rewrite skipn_all. cbn [reply_matches_items]. rewrite Hb0. reflexivity.
Qed.
End e.
End f.
End d.
(* Tactics the segments share. [srm_kept HS HAE l HK]: the registers of [l] that the run did not write keep their
   values; [srm_rgoal HS] turns [getr (ms_regs ms) r = w64 z] into a statement over the symbolic value;
   [srm_ucalc] evaluates such a value over the walk's atoms (facts [bv_unsigned (ew E n) = v] in the context). *)
Ltac srm_kept HS HAE l HK :=
  lazymatch type of HS with context [restrict _ ?msn] =>
  lazymatch type of HAE with env_agree _ (Ereg ?rg ?ex) _ =>
  assert (HK : forall r, In r l -> getr (ms_regs msn) r = getr rg r)
    by (intros r Hr; pose proof (regs_kept_of_st_ok_pi _ _ _ rg ex l HS) as HKs;
        cbn [ms_regs restrict] in HKs; apply HKs; [env_agree_chain HAE | vm_compute; reflexivity | exact Hr])
  end end.
Ltac srm_rgoal HS :=
  lazymatch goal with |- getr (ms_regs ?msn) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS);
    lazymatch goal with |- sv_denot _ (sr_get ?sr _) = _ =>
      let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end;
    apply sv_w64 end.
Ltac srm_ucalc :=
  repeat (rewrite U_SAlu || rewrite U_SOff || rewrite U_SLit || rewrite U_SExt); cbn [zalu_raw ew ewset Nat.eqb];
  repeat match goal with V : bv_unsigned (ew ?E ?n) = _ |- _ => rewrite V end;
  unfold zcanon, M64; rewrite ?Z.add_0_r.
(* the same at a call: the state is [st_ok] at the callee's address *)
Ltac srm_kept_c HS HAE l HK :=
  lazymatch type of HS with context [restrict _ ?msn] =>
  lazymatch type of HAE with env_agree _ (Ereg ?rg ?ex) _ =>
  assert (HK : forall r, In r l -> getr (ms_regs msn) r = getr rg r)
    by (intros r Hr; pose proof (regs_kept_of_st_ok _ _ _ _ rg ex l HS) as HKs;
        cbn [ms_regs restrict] in HKs; apply HKs; [env_agree_chain HAE | vm_compute; reflexivity | exact Hr])
  end end.
