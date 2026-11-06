(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths and module names changed; 511 of its 639 lines of code are new or changed and 1464 lines of the source are left out. *)
(* reac_declared_vlan_add on fuzz_segconf.asan-ubsan (image B, entry BASE + AF_reac_declared_vlan_add = 0x8a514, 177
   instructions, 112-byte frame, no side-stack frame): segment 0 of the walk of lib/B/Prog/reac_declared_vlan_add_c.v,
   the image-B port of lib/A/Prog/reac_declared_vlan_add_s0.v (commit fcd2fa03dd27). Written for
   the image-B G4 + G5 walks, in the form of plugin-hostd/fuzz_command's released lib/B/Prog walks (the symbolic
   executor over the position-abstract listing, the inline checks removed by the shadow tokens, the loop cut at its
   head and re-seeded there, each UBSan trap branch refuted at the branch).
   This segment: the image-B numbers, the cut points and what holds at each, the facts of the entry every stretch
   uses, the epilogue (0x8a720) and the exit that keeps the table (a duplicate: 0; full: -1). The stretches are
   segments 1 .. 5 (reac_declared_vlan_add_s1.v .. _s5.v); reac_declared_vlan_add.v composes them.
   Image B's code differs from image A's (ADAPTED): the frame keeps the shadow address of the count cell in its
   lowest slot (sd a0,0(sp) at 0x8a58c; reloaded at 0x8a654, 0x8a698, 0x8a6ec, 0x8a704), the search loop keeps tab in
   s7, the count in s9 and the cursors in s2 / s6, and UBSan adds the tests that branch to the trap `unimp` 0x8a760. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase reac_declared_vlan_add_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_add_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- readers: carrying byte facts across a state that agrees outside a window ---------- *)
Definition vad_kept (rd rd' : reader) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma vad_kept_trans : forall rd1 rd2 rd3 lo hi lo' hi',
vad_kept rd1 rd2 lo hi -> vad_kept rd2 rd3 lo' hi' -> lo <= lo' -> hi' <= hi -> vad_kept rd1 rd3 lo hi.
Proof. intros rd1 rd2 rd3 lo hi lo' hi' H12 H23 Hl Hh a Ha Hn. rewrite (H23 a Ha) by lia. exact (H12 a Ha Hn). Qed.
Lemma vad_sa_bytes_keep : forall (rd rd' : reader) (P : Z -> Prop) a bs,
(forall x, P x -> rd' x = rd x) -> sa_bytes rd a bs ->
(forall i, (i < length bs)%nat -> P (a + Z.of_nat i)) -> sa_bytes rd' a bs.
Proof. intros rd rd' P a bs HK H HP i Hi. rewrite (HK _ (HP i Hi)). exact (H i Hi). Qed.
Lemma vad_sa_val_keep : forall (rd rd' : reader) (P : Z -> Prop) a k v,
(forall x, P x -> rd' x = rd x) -> sa_val rd a k v ->
(forall i, (i < k)%nat -> P (a + Z.of_nat i)) -> sa_val rd' a k v.
Proof. intros rd rd' P a k v HK H HP i Hi. rewrite (HK _ (HP i Hi)). exact (H i Hi). Qed.
Lemma vad_sa_rtab_keep : forall (rd rd' : reader) (P : Z -> Prop) a t,
(forall x, P x -> rd' x = rd x) -> sa_rtab rd a t ->
(forall i, (i < 18 * length t)%nat -> P (a + Z.of_nat i)) -> sa_rtab rd' a t.
Proof.
intros rd rd' P a t HK (bs & Hb & He) HP. exists bs. split; [|exact He].
apply (vad_sa_bytes_keep rd rd' P a bs HK Hb). intros i Hi. apply HP. destruct He as [HL _]. lia.
Qed.
Lemma vad_val_mem_of_sa : forall segs H mem a k v, sa_val (aview segs H mem) a k v -> val_mem segs (mrestrict H mem) a k v.
Proof.
intros segs H mem a k v Hr i Hi. pose proof (Hr i Hi) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma vad_sa_of_val_mem : forall segs H m0 x k v, val_mem segs (mrestrict H m0) x k v -> sa_val (aview segs H m0) x k v.
Proof.
intros segs H m0 x k v Hv i Hi. unfold aview. rewrite (Hv i Hi). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
(* the shadow facts of a range survive a change of the memory away from its shadow cells *)
Lemma vad_ra_keep : forall (rd rd' : reader) (P : Z -> Prop) a len, (forall y, P y -> rd' y = rd y) ->
range_addressable rd SHADOW_OFF a len -> (forall x, a <= x < a + len -> P (shadow_of_addr SHADOW_OFF x)) ->
range_addressable rd' SHADOW_OFF a len.
Proof. intros rd rd' P a len HK H HP x Hx. rewrite (HK _ (HP x Hx)). exact (H x Hx). Qed.
Lemma vad_hull_keep : forall (rd rd' : reader) (P : Z -> Prop) a len, (forall y, P y -> rd' y = rd y) ->
shadow_hull_vis rd a len ->
(forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + len - 1) / 8 * 8 + 8 -> P s) ->
shadow_hull_vis rd' a len.
Proof. intros rd rd' P a len HK H HP s Hs. rewrite (HK _ (HP s Hs)). exact (H s Hs). Qed.
Lemma vad_sa_bytes_app : forall rd a l1 l2, sa_bytes rd a (l1 ++ l2) <-> sa_bytes rd a l1 /\ sa_bytes rd (a + Z.of_nat (length l1)) l2.
Proof.
intros rd a l1 l2. split.
- intros H. split.
  + intros i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
  + intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
    rewrite (H (length l1 + i)%nat ltac:(rewrite length_app; lia)). rewrite app_nth2 by lia.
    replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
- intros [H1 H2] i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length l1)) as [Hlt|Hge].
  + rewrite (H1 i Hlt). rewrite app_nth1 by exact Hlt. reflexivity.
  + replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
    rewrite (H2 (i - length l1)%nat ltac:(lia)). rewrite app_nth2 by exact Hge. reflexivity.
Qed.

(* ---------- one entry of the table through a reader ---------- *)
Lemma vad_bytes_sub : forall rd a (l : list byte) k n, sa_bytes rd a l -> (k + n <= length l)%nat ->
  sa_bytes rd (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
intros rd a l k n H Hk i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [_|]; [|lia]. rewrite nth_skipn.
replace (i + k)%nat with (k + i)%nat by lia. apply H. lia.
Qed.
(* entry i of the reader's table: the vid's two bytes at tab + 18 i + 16, and the parent's string with its NUL at
   tab + 18 i (the plain walk's form; check_declared's cd_rtab_entry over vad_entry_fields) *)
Lemma vad_rtab_entry : forall rd tab t bt i, sa_bytes rd tab bt -> seg_spec.rtab_enc t bt -> (i < length t)%nat ->
  sa_val rd (tab + 18 * Z.of_nat i + 16) 2 (snd (nth i t ([], 0))) /\
  0 <= snd (nth i t ([], 0)) < 65536 /\
  exists sx, sa_bytes rd (tab + 18 * Z.of_nat i) (sx ++ [Z_to_bv 8 0]) /\ seg_spec.zs sx = fst (nth i t ([], 0)) /\
             ~ In (Z_to_bv 8 0) sx /\ (length sx < 16)%nat.
Proof.
intros rd tab t bt i HB HE Hi.
destruct (vad_entry_fields t bt i HE Hi) as (sx & Zsx & Nsx & Lsx & Hs & Hv & Hvid & Hlen).
split; [|split; [exact Hv|]].
- intros k Hk. replace (tab + 18 * Z.of_nat i + 16 + Z.of_nat k) with (tab + Z.of_nat (18 * i + 16 + k)) by lia.
  rewrite (HB (18 * i + 16 + k)%nat) by lia. unfold ZB0. rewrite (Hvid k Hk). f_equal.
  unfold le_byte. apply vad_le2_byte; [exact Hv | exact Hk].
- exists sx. split; [|split; [exact Zsx | split; [exact Nsx | exact Lsx]]].
  intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  replace (tab + 18 * Z.of_nat i + Z.of_nat k) with (tab + Z.of_nat (18 * i + k)) by lia.
  rewrite (HB (18 * i + k)%nat) by lia. unfold ZB0. rewrite (Hs k ltac:(lia)). reflexivity.
Qed.

(* ---------- image B's numbers ---------- *)
(* the stack a call needs below its entry sp, image B's instance file's SegInstB.STK_reac_declared_vlan_add (8,304),
   under the name the segments use: its frame of 112 bytes (addi sp,sp,-112 at 0x8a514) and, below it, the deepest
   window of an entry it calls (RtString.astrcmp_realizes and RtSeg.astrncpy_realizes: 2 * ESTACK; the checked
   memset: ESTACK) *)
Notation VAD_STK := SegInstB.STK_reac_declared_vlan_add (only parsing).
(* listing offsets from BASE (image B: BASE + 0x5754 = 0x8a514, so BASE = 0x84dc0) *)
Definition VAD_LH : Z := 0x57f8.   (* 0x8a5b8, the search loop's head (beqz s2, the first UBSan test) *)
Definition VAD_RCMP : Z := 0x582c. (* 0x8a5ec, the strcmp call's return *)
Definition VAD_LT : Z := 0x5830.   (* 0x8a5f0, the search loop's latch *)
Definition VAD_AFT : Z := 0x5854.  (* 0x8a614, bge s9, s5 *)
Definition VAD_RMS : Z := 0x5894.  (* 0x8a654, the checked memset's return *)
Definition VAD_RSN : Z := 0x58d8.  (* 0x8a698, the strncpy call's return *)
Definition VAD_ST : Z := 0x5914.   (* 0x8a6d4, addi a0,a0,16: a0 = tab + 18 count *)
Definition VAD_DUP : Z := 0x595c.  (* 0x8a71c, li s4,0 *)
Definition VAD_EPI : Z := 0x5960.  (* 0x8a720, mv a0, s4 *)
Definition VAD_TRAP : Z := 0x59a0. (* 0x8a760, the UBSan trap unimp *)
(* the frame: ra and s0 .. s11 at sp0 - 8 .. sp0 - 104; the shadow address of the count cell at sp0 - 112 *)
Definition vad_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition vad_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition vad_SBF : afact := mkAF SB SB 0.
Definition vad_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition vad_Bx : sv := SOff 32 0.
(* the shadow address of the n-th atom: what srli/add compute at 0x8a584 .. 0x8a588 *)
Definition vad_shx (k : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k 0) (SLit 3)) (SOff 32 0).
(* the epilogue's symbolic state: the frame's 13 saved words as atoms 32 .. 44 *)
Definition vad_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0
  (map (fun j => YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13)).
Definition vad_ss_epi : sstate := mkSS VAD_EPI sr_atoms [vad_estack] None (mkFacts [(2%nat, vad_spF)] [] []).

Lemma vad_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= x / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_add64 : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y Hx Hy Hxy. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_shx_val : forall x, 0 <= x < 2 ^ 47 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = w64 (SB + x / 8).
Proof.
intros x Hx. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite vad_srl3 by lia. unfold w64, SB. rewrite vad_add64 by lia. f_equal. lia.
Qed.
Lemma vad_shx_U : forall E k x, ew E 32 = w64 SB -> ew E k = w64 x -> 0 <= x < 2 ^ 47 ->
sv_denot E (vad_shx k) = w64 (SB + x / 8).
Proof.
intros E k x H32 Hk Hx. unfold vad_shx. cbn [sv_denot]. rewrite H32, Hk, !Z.add_0_r.
unfold w64. rewrite !Z_to_bv_bv_unsigned. apply vad_shx_val. exact Hx.
Qed.
Lemma vad_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vad_bge0 : forall E k v, ew E k = w64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (v <=? 0).
Proof.
intros E k v Hk Hv. cbn [branch_taken sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !vad_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
(* the shadow bytes an interceptor's range check reads of [x, x + len) lie in the shadow band *)
Lemma vad_hull_band : forall x len s, 0 <= x -> x + len <= 2 ^ 47 - 64 -> 0 < len ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + len - 1) / 8 * 8 + 8 -> SB <= s < SB + 2 ^ 44.
Proof.
intros x len s Hx Hl Hn Hs. unfold shadow_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs. unfold SB in *.
assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H2 : (x + len - 1) / 8 < 2 ^ 44 - 7) by (apply Z.div_lt_upper_bound; lia).
assert (H3 : 2147450880 <= (2147450880 + x / 8) / 8 * 8).
{ replace (2147450880 + x / 8) with (x / 8 + 268431360 * 8) by lia. rewrite Z.div_add by lia.
  pose proof (Z.div_pos (x / 8) 8 ltac:(lia) ltac:(lia)). lia. }
assert (H4 : 8 * ((2147450880 + (x + len - 1) / 8) / 8) <= 2147450880 + (x + len - 1) / 8) by (apply Z.mul_div_le; lia).
lia.
Qed.
Lemma vad_set_fs_self : forall S : astate, exists f, S = set_fs f S.
Proof. intros S. destruct S. eexists. unfold set_fs. cbn. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the extra words of a seed *)
Lemma vad_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof using.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.

(* the shadow of a range a check reads *)
Lemma vad_shent_ok : forall E (H : word -> bool) mem' k x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E k) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
range_addressable (aview SEGS H mem') SHADOW_OFF (x + lo) (hi - lo) ->
(forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
shent_ok SEGS vad_Bx E (mrestrict H mem') (mkSHE k lo hi).
Proof using.
intros E H mem' k x lo hi H32 Hk H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, vad_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hk; pose proof (bv_unsigned_in_range 64 (ew E k)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Uk : U E (SOff k 0) = x) by (rewrite U_SOff, Hk, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Uk. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
(* a 8-byte word of the stack region of a symbolic state, at its value *)
Lemma vad_stack_word : forall E H mem' sp lo hi wlo whi cs off e v,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
sa_val (aview SEGS H mem') (sp + off) 8 v.
Proof using.
intros E H mem' sp lo hi wlo whi cs off e v HR Hsp Hin He Hv. apply vad_sa_of_val_mem.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 sp cs lo hi wlo whi off 8 e v HR Hsp Hin).
- exact He.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac vad_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac vad_keep_empty HFr K :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : forall x, 0 <= x < 2 ^ 64 -> aview SEGS H m2 x = aview SEGS H m1 x)
  by (intros x0 Hx0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.

(* ---------- one call of reac_declared_vlan_add ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (rlo rhi tab max n par vid : Z) (t : list (list Z * Z)) (p : list Z).
Hypothesis HPRE : afn_pre SEGS B VAD_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS rlo rhi B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 tab.
Hypothesis H11 : getr regs 11 = w64 max.
Hypothesis H12 : getr regs 12 = w64 n.
Hypothesis H13 : getr regs 13 = w64 par.
Hypothesis H14 : getr regs 14 = w64 vid.
Hypothesis HADD : add_pre SEGS B ly S W mem regs tab max n par vid t p.

#[local] Notation L := (Z.of_nat (length t)).
#[local] Notation VA := (vlan_add t max p vid).
#[local] Notation sp0 := (spZ regs).
#[local] Notation VD := (tab + 18 * Z.of_nat (length t)).
Definition vad_FP : list (Z * Z) := vtab_W tab n t (snd (vlan_add t max p vid)).
Definition vad_E : Z -> Prop := vtab_E tab n t (snd (vlan_add t max p vid)).

(* the contract's post at this call (EV_reac_declared_vlan_add = 0) *)
Definition vad_Q : world SEGS -> config -> Prop :=
apost_base SEGS B VAD_STK vad_FP regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (fst VA) /\
 sa_rtab (rdW W' mem') tab (snd VA) /\
 sa_val (rdW W' mem') n 4 (Z.of_nat (length (snd VA))) /\
 (sa_guardtab (rdW W mem) tab max -> sa_guardtab (rdW W' mem') tab max) /\
 sa_kept SEGS W mem W' mem' regs VAD_STK vad_E /\
 sa_noalloc B ly S ly' S').

(* the saved registers in the frame *)
Definition vad_frame (rd : reader) : Prop :=
forall j r, nth_error vad_saved j = Some r ->
sa_val rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the frame's lowest slot: the shadow address of the count cell (sd a0,0(sp) at 0x8a58c) *)
Definition vad_spill (rd : reader) : Prop := sa_val rd (sp0 - 112) 8 (SB + n / 8).
(* a point after the prologue: the journal from the entry, the frame, sp, gp, tp *)
Definition vad_cutE (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B VAD_STK sp0 vad_FP ly S W mem md [] ly S W mem1 md1 0 /\
vad_frame (rdW W mem1) /\
getr regs1 2 = w64 (sp0 - 112) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4.
(* a point before the append: also the memory outside the stack window unchanged *)
Definition vad_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cutE regs1 mem1 md1 /\ vad_kept (rdW W mem) (rdW W mem1) (sp0 - VAD_STK) sp0.
(* the registers every cut after the entry stretch carries *)
Definition vad_regs (regs1 : bvmap 5 word) : Prop :=
getr regs1 8 = w64 n /\ getr regs1 9 = w64 vid /\ getr regs1 19 = w64 par /\ getr regs1 20 = w64 (-1) /\
getr regs1 21 = w64 max /\ getr regs1 23 = w64 tab /\ getr regs1 24 = w64 SB /\ getr regs1 25 = w64 L.
(* the search loop's head (0x8a5b8), entry i; entries 0 .. i - 1 did not match *)
Definition vad_LHc (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ vad_spill (rdW W mem1) /\ (i < length t)%nat /\
existsb (vad_match vid p) t = existsb (vad_match vid p) (skipn i t) /\
getr regs1 18 = w64 (tab + 18 * Z.of_nat i) /\ getr regs1 22 = w64 (tab + 18 * Z.of_nat i) /\
getr regs1 26 = w64 0 /\ getr regs1 27 = w64 (L - Z.of_nat i).
(* the latch (0x8a5f0) after entry i, which did not match *)
Definition vad_LTc (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ vad_spill (rdW W mem1) /\ (i < length t)%nat /\
existsb (vad_match vid p) t = existsb (vad_match vid p) (skipn (Datatypes.S i) t) /\
getr regs1 18 = w64 (tab + 18 * Z.of_nat i) /\ getr regs1 22 = w64 (tab + 18 * Z.of_nat i) /\
getr regs1 26 = w64 0 /\ getr regs1 27 = w64 (L - Z.of_nat i).
(* after the search (0x8a614): no entry matches *)
Definition vad_AFTc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cut regs1 mem1 md1 /\ vad_regs regs1 /\ vad_spill (rdW W mem1) /\ existsb (vad_match vid p) t = false.
(* the checked memset's return (0x8a654) on the append path: tab[count] reads 0, every other byte outside the stack
   window as at the entry *)
Definition vad_MSc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cutE regs1 mem1 md1 /\ vad_regs regs1 /\ getr regs1 18 = w64 18 /\ vad_spill (rdW W mem1) /\
L < max /\ existsb (vad_match vid p) t = false /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - VAD_STK <= x < sp0) -> ~ (VD <= x < VD + 18) -> rdW W mem1 x = rdW W mem x) /\
(forall k, 0 <= k < 18 -> rdW W mem1 (VD + k) = Some 0).
(* the strncpy call's return (0x8a698) on the append path: tab[count]'s first 16 bytes are the new entry's *)
Definition vad_SNc (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
vad_cutE regs1 mem1 md1 /\ vad_regs regs1 /\ getr regs1 18 = w64 18 /\ vad_spill (rdW W mem1) /\
L < max /\ existsb (vad_match vid p) t = false /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - VAD_STK <= x < sp0) -> ~ (VD <= x < VD + 18) -> rdW W mem1 x = rdW W mem x) /\
(exists f16, length f16 = 16%nat /\ sa_bytes (rdW W mem1) VD f16 /\
  seg_spec.rvlan_enc (firstn 15 (cut_nul p), vid) (f16 ++ Mem.le2 (Z_to_bv 64 vid))).

(* ---------- the facts of the entry that every stretch uses ---------- *)
Lemma vad_sp : sp0 mod 16 = 0 /\ alloc_ceiling + VAD_STK <= sp0 /\ sp0 <= 2 ^ 47 /\ alloc_ceiling mod 4096 = 0.
Proof using HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof alloc_ceiling_value as [_ HAC]. repeat split; lia.
Qed.
Lemma vad_STK_val : VAD_STK = 8304.
Proof using. reflexivity. Qed.
Lemma vad_noalloc : sa_noalloc B ly S ly S.
Proof using. split; [apply Permutation_refl|]. split; [reflexivity|]. apply vad_set_fs_self. Qed.
(* the table: a live block below the heap's ceiling, in application memory, present, its shadow addressable *)
Lemma vad_tab_facts :
4096 <= tab /\ tab + 18 * (max + 1) <= alloc_ceiling /\ L <= max < 2 ^ 31 /\ tab mod 16 = 0 /\
(forall x, tab <= x < tab + 18 * (max + 1) -> ~ (SB <= x < SB + 2 ^ 44)) /\
(forall x, tab <= x < tab + 18 * (max + 1) -> apresent (w_H W) mem x) /\
(forall x, tab <= x < tab + 18 * (max + 1) -> ~ in_img SEGS x) /\
(tab + 18 * (max + 1) <= 0x10000 \/ 0x602000 <= tab).
Proof using HPRE HADD LAWS.
pose proof HPRE as (HAR & _).
destruct HADD as ((Htab0 & Htab16 & HRT & HLm & (b & m & Hbm & Hb1 & Hb2) & _) & _).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos m ltac:(unfold seg_spec.RVLAN_SIZE in *; lia)) as [_ Hreq].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold seg_spec.RVLAN_SIZE in *.
pose proof (blk_off_imgP B ly S W mem md b m HAR Hbm) as Hoi. unfold off_img in Hoi.
split; [lia|]. split; [lia|]. split; [exact HLm|]. split; [exact Htab16|]. split.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *. lia.
- split; [intros x Hx; exact (proj1 (Hppres x ltac:(lia)))|].
  split; [intros x Hx; exact (blk_img SEGS B LAWS ly S W mem md b m x HAR Hbm ltac:(lia))|].
  lia.
Qed.
(* the count cell: outside the stack window, in application memory, apart from the table block *)
Lemma vad_n_facts :
4096 <= n /\ n + 4 <= 2 ^ 47 /\ n mod 4 = 0 /\ (n + 4 <= alloc_ceiling \/ sp0 <= n) /\
(forall x, n <= x < n + 4 -> ~ (SB <= x < SB + 2 ^ 44)) /\
(n + 4 <= tab \/ tab + 18 * (max + 1) <= n) /\ (n + 4 <= 0x10000 \/ 0x602000 <= n).
Proof using HPRE HADD LAWS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HADD as ((_ & _ & _ & _ & _ & _ & _ & Hn0 & Hn4 & _ & HDST & _ & HDJ) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LT : kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & _ & _ & L3). exact L3. }
unfold sa_disj, seg_spec.RVLAN_SIZE in HDJ.
destruct HDST as [((cid & pos & Hin & Hcid & Hf1 & Hf2) & _) | [((b & m & Hbm & Hb1 & Hb2) & _) | (Hs1 & Hs2 & _)]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4 & Hfc & Hfa).
  pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hin) as Hoi. unfold off_img in Hoi.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
  repeat split; try lia; intros x Hx; lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
  pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
  pose proof (blk_off_imgP B ly S W mem md b m HAR Hbm) as Hoi. unfold off_img in Hoi.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
  repeat split; try lia; intros x Hx; lia.
- unfold kHighMemBeg, SB in *. repeat split; try lia; intros x Hx; lia.
Qed.
(* every image byte lies outside the stack window, the table block and the count cell *)
Lemma vad_img_out : forall x, in_img SEGS x ->
0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0) /\ ~ (tab <= x < tab + 18 * (max + 1)) /\ ~ (n <= x < n + 4).
Proof using HPRE HADD LAWS.
intros x Hx. pose proof (pa_img_range _ Hx) as HR. unfold kImgEnd in HR.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_STK_val as HST.
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
pose proof vad_n_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
split; [lia|]. split; [lia|]. split; [intros Hin; exact (T7 x Hin Hx)|]. lia.
Qed.

(* the read-only view the runtime entries ask, at a state whose image bytes read as at the entry *)
Lemma vad_rom_at : forall memc, (forall x, in_img SEGS x -> rdW W memc x = rdW W mem x) ->
rt_rom_view SEGS B W memc.
Proof using HROD.
intros memc HK x Hx Ho He.
destruct Hx as (sg & Hsg & Hw & Hr).
assert (Himg : in_img SEGS x) by (exists sg; split; [exact Hsg | exact Hr]).
rewrite (HK x Himg).
apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He].
Qed.

(* the parent string at a call, at a state whose bytes outside the stack window and the table block read as at the
   entry: what RtString.astrcmp_realizes and RtSeg.astrncpy_realizes ask of it *)
Lemma vad_par_call : forall memc regsc,
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - VAD_STK <= y < sp0) -> ~ (tab <= y < tab + 18 * (max + 1)) -> rdW W memc y = rdW W mem y) ->
spZ regsc = sp0 - 112 ->
0 < par /\ astr_at SEGS W memc par (seg_spec.zb p) /\ astr_len (seg_spec.zb p) = Z.of_nat (length p) /\
aread_ok SEGS (2 * ESTACK) W regsc memc par (Z.of_nat (length p) + 1) /\
atail_vis SEGS W memc (par + Z.of_nat (length p)) /\ amem_range par (Z.of_nat (length p) + 8) /\
Z.of_nat (length p) + 1 < 2 ^ 32 /\ par + Z.of_nat (length p) + 1 <= alloc_ceiling /\
(par + seg_spec.cstr_span par p <= tab \/ tab + 18 * (max + 1) <= par).
Proof using HPRE HADD LAWS.
intros memc regsc HK Hsp.
pose proof HPRE as (HAR & _). pose proof vad_sp as (Hal16 & Hslo & Hshi & HAC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof vad_tab_facts as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
destruct HADD as (_ & Hp0 & HSTR & HPA & Hp32 & HPR & HLOC & HDJ & Hvid).
pose proof HDJ as HDJ0.
destruct HPA as (PA0 & PA1 & PA2 & PA3 & PA4).
unfold sa_disj, seg_spec.cstr_span, seg_spec.RVLAN_SIZE in HDJ.
set (lp := Z.of_nat (length p)) in *.
assert (Hlp : 0 <= lp) by lia.
pose proof (vad_word_end (par + lp)) as HWE.
pose proof (Z.mod_pos_bound (par + lp) 8 ltac:(lia)) as Hm8.
(* where the parent lies: below alloc_ceiling *)
assert (HLO : par + lp + 1 <= alloc_ceiling).
{ destruct HLOC as [(b & m & Hbm & Hb1 & Hb2) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | HIMG]].
  - destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & _ & Hpceil & Hpapp & _).
    pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq]. lia.
  - destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4 & Hfc & Hfa). lia.
  - destruct (HIMG (par + lp) ltac:(lia)) as (Hi2 & _).
    pose proof (pa_img_range _ Hi2) as R2. unfold kImgEnd in R2. lia. }
(* the tail word ends at or below alloc_ceiling *)
assert (HTW : par + lp - (par + lp) mod 8 + 8 <= alloc_ceiling) by (apply tail_below; lia).
assert (HKp : forall y, par <= y < par + lp - (par + lp) mod 8 + 8 -> rdW W memc y = rdW W mem y).
{ intros y Hy. apply HK; lia. }
destruct (sa_strz_bytes SEGS (w_H W) mem par p (proj1 HSTR)) as (HB & HN0 & HZ).
assert (Hlen : astr_len (seg_spec.zb p) = lp) by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
assert (HP : forall y, (0 <= y < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= y < sp0) /\ ~ (tab <= y < tab + 18 * (max + 1))) ->
  rdW W memc y = rdW W mem y) by (intros y (Hy1 & Hy2 & Hy3); exact (HK y Hy1 Hy2 Hy3)).
split; [lia|]. split.
{ split; [|exact HN0]. intros i Hi. rewrite length_app in Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi.
  cbn [length] in Hi. rewrite (HKp (par + Z.of_nat i)) by lia.
  apply (HB i). rewrite length_app. unfold seg_spec.zb. rewrite length_map. cbn [length]. lia. }
split; [exact Hlen|]. split.
{ split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros a Ha. split; [|unfold ascratch_stk; rewrite Hsp; lia].
    rewrite (HKp a) by lia.
    pose proof (proj1 (proj1 HSTR) (Z.to_nat (a - par)) ltac:(rewrite length_app; cbn [length]; lia)) as E.
    replace (par + Z.of_nat (Z.to_nat (a - par))) with a in E by lia. rewrite E. discriminate. }
  split; [exact PA2|]. split.
  - apply (vad_ra_keep (rdW W mem) _ _ _ _ HP PA3).
    intros x Hx. cbv beta. rewrite <- SB_SHADOW_OFF. unfold shadow_of_addr.
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    split; [unfold SB; lia|]. split; [unfold SB; lia|].
    intros Hin. apply (T5 (SB + x / 8)); [lia | unfold SB; lia].
  - intros Hn0. apply (vad_hull_keep (rdW W mem) _ _ _ _ HP (PA4 Hn0)).
    intros s Hs. cbv beta. pose proof (vad_hull_band par (lp + 1) s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hb.
    split; [unfold SB in *; lia|]. split; [unfold SB in *; lia|].
    intros Hin. exact (T5 s Hin Hb). }
split.
{ intros a Ha. rewrite (HKp a) by lia. destruct HSTR as (_ & HT). apply (HT a). exact Ha. }
split; [exact HPR|]. split; [lia|]. split; [lia|].
exact HDJ0.
Qed.

(* ---------- the epilogue: 0x8a720 .. 0x8a75c, a0 = s4, ra and s0 .. s11 restored, ret ---------- *)
Definition vad_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) vad_saved.
Lemma vad_e_nth : forall j r, nth_error vad_saved j = Some r -> nth j vad_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof using. intros j r H. unfold vad_e_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j vad_saved H). reflexivity. Qed.
Lemma vad_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (sp0 - 112) -> vad_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 vad_e_extra)) vad_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS vad_Bx [] (Eimg (Ereg regs1 vad_e_extra)) (mrestrict (w_H W) mem1).
Proof using HPRE.
intros regs1 mem1 R2 HFR. pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
set (E := Eimg (Ereg regs1 vad_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold vad_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vad_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error vad_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (sp0 - 112) (104 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (vad_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (sp0 - 112 + (104 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
    apply vad_val_mem_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, vad_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma vad_epi : forall v regs1 mem1 md1, vad_cutE regs1 mem1 md1 -> getr regs1 20 = w64 v -> v = fst VA ->
sa_rtab (rdW W mem1) tab (snd VA) -> sa_val (rdW W mem1) n 4 (Z.of_nat (length (snd VA))) ->
(sa_guardtab (rdW W mem) tab max -> sa_guardtab (rdW W mem1) tab max) ->
sa_kept SEGS W mem W mem1 regs VAD_STK vad_E ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using HPRE HADD TL.
intros v regs1 mem1 md1 (HJ & HFR & R2 & R3 & R4) R20 Hv HT HN HGd HKP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
destruct (vad_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 vad_e_extra))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 vad_e_extra)) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j r, nth_error vad_saved j = Some r -> ew (Eimg (Ereg regs1 vad_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (vad_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 vad_e_extra)) 2) = sp0 - 112).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39. pose proof (EX 8%nat 23 eq_refl) as E40.
pose proof (EX 9%nat 24 eq_refl) as E41. pose proof (EX 10%nat 25 eq_refl) as E42. pose proof (EX 11%nat 26 eq_refl) as E43.
pose proof (EX 12%nat 27 eq_refl) as E44.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 20%nat 20%bv eq_refl) as E20.
clear EX.
remember (Eimg (Ereg regs1 vad_e_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
vad_md.
vad_keep_empty HFr KE.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold vad_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (sp0 - 112 + 112) with sp0 by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity
          | rewrite E37; reflexivity | rewrite E38; reflexivity | rewrite E39; reflexivity | rewrite E40; reflexivity
          | rewrite E41; reflexivity | rewrite E42; reflexivity | rewrite E43; reflexivity | rewrite E44; reflexivity ] ]. }
split; [rewrite F10, E20, R20, Hv; reflexivity|].
split.
{ apply (vad_sa_rtab_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ (fun x Hx => KE x Hx) HT).
  intros i Hi. pose proof vad_tab_facts as (T1 & T2 & T3 & _).
  pose proof (vad_vlan_add_len t max p vid (proj1 T3)) as [VL1 VL2]. lia. }
split.
{ apply (vad_sa_val_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ _ (fun x Hx => KE x Hx) HN).
  intros i Hi. pose proof vad_n_facts as (N1 & N2 & _). lia. }
split.
{ intros HGg. apply (vad_sa_bytes_keep _ _ (fun x => 0 <= x < 2 ^ 64) _ _ (fun x Hx => KE x Hx) (HGd HGg)).
  intros i Hi. pose proof vad_tab_facts as (T1 & T2 & T3 & _). unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi.
  cbv beta. unfold seg_spec.RVLAN_SIZE. lia. }
split.
{ intros a Ha Hw He. rewrite (KE a Ha). exact (HKP a Ha Hw He). }
exact vad_noalloc.
Qed.

(* the exit with the table unchanged (a duplicate: 0; full: -1): the table, the count and the guard lie outside the
   stack window, which is all the memory the walk has changed *)
Lemma vad_keep : forall v regs1 mem1 md1, vlan_add t max p vid = (v, t) -> vad_cut regs1 mem1 md1 -> getr regs1 20 = w64 v ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + VAD_EPI)) mem1 (seg_rom SEGS)) md1) vad_Q.
Proof using HPRE HADD TL LAWS.
intros v regs1 mem1 md1 EVA (HC & HK) R20.
pose proof vad_sp as (Hal16 & Hlo & Hhi & _).
pose proof vad_tab_facts as (T1 & T2 & T3 & _). pose proof vad_n_facts as (N1 & N2 & N3 & N4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
pose proof HADD as ((_ & _ & HRT & _ & _ & _ & _ & _ & _ & HNV & _) & _).
assert (HKP : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp0 - VAD_STK <= x < sp0)) -> rdW W mem1 x = rdW W mem x)
  by (intros x [Hx1 Hx2]; exact (HK x Hx1 Hx2)).
apply (vad_epi v regs1 mem1 md1 HC R20); rewrite ?EVA; cbn [fst snd]; [reflexivity | | | |].
- apply (vad_sa_rtab_keep _ _ _ _ _ HKP HRT). intros i Hi. cbv beta. lia.
- apply (vad_sa_val_keep _ _ _ _ _ _ HKP HNV). intros i Hi. cbv beta. lia.
- intros HG. apply (vad_sa_bytes_keep _ _ _ _ _ HKP HG). intros i Hi. cbv beta.
  unfold seg_spec.GUARD_BYTES in Hi. rewrite repeat_length in Hi. unfold seg_spec.RVLAN_SIZE. lia.
- intros a Ha Hw _. exact (HK a Ha Hw).
Qed.

(* ---------- carrying a cut ---------- *)
(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma vad_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
vad_cut regs1 mem1 md1 ->
ajournal SEGS B VAD_STK sp0 vad_FP ly S W mem md [] ly S W mem2 md2 0 ->
vad_kept (rdW W mem1) (rdW W mem2) lo hi -> sp0 - VAD_STK <= lo -> hi <= sp0 - 112 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
vad_cut regs2 mem2 md2.
Proof using HPRE.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi ((HJ & HFR & R2 & R3 & R4) & HK) HJ2 HK2 Hlo Hhi Q2 Q3 Q4.
pose proof vad_sp as (Hal16 & Hslo & Hshi & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof vad_STK_val as HST.
split; [split; [exact HJ2|]; split|].
- intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length vad_saved); apply (proj1 (nth_error_Some vad_saved j)); rewrite Hr; discriminate).
  apply (vad_sa_val_keep (rdW W mem1) _ (fun x => 0 <= x < 2 ^ 64 /\ ~ (lo <= x < hi))); [intros x [Hx1 Hx2]; exact (HK2 x Hx1 Hx2) | exact (HFR j r Hr) |].
  intros k Hk. cbv beta. lia.
- split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3 | rewrite Q4; exact R4].
- intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn).
Qed.
(* the spill slot carried the same way *)
Lemma vad_spill_kept : forall mem1 mem2 lo hi, vad_spill (rdW W mem1) ->
vad_kept (rdW W mem1) (rdW W mem2) lo hi -> hi <= sp0 - 112 -> vad_spill (rdW W mem2).
Proof using HPRE.
intros mem1 mem2 lo hi HSP HK Hhi. pose proof vad_sp as (Hal16 & Hslo & Hshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof vad_STK_val as HST.
unfold vad_spill in *. intros k Hk. rewrite (HK (sp0 - 112 + Z.of_nat k)) by lia. exact (HSP k Hk).
Qed.
(* the frame, read back from the stack region (based at the entry sp) of a symbolic state *)
Lemma vad_frm : forall E H mem' lo hi wlo whi cs,
(forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) ->
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
(forall j r, nth_error vad_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
vad_frame (aview SEGS H mem').
Proof using.
intros E H mem' lo hi wlo whi cs EE HR Hin j r Hr.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hr' : 1 <= r <= 27) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
apply (vad_stack_word E H mem' sp0 lo hi wlo whi cs _ (SOff (Z.to_nat r) 0)); [exact HR | exact Usp | exact (Hin j r Hr) | |
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite !Z_to_bv_bv_unsigned; reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.

(* ---------- the append path ---------- *)
Lemma vad_FP_app : existsb (vad_match vid p) t = false -> L < max ->
vad_FP = [(VD, VD + 18); (n, n + 4)].
Proof using.
intros HEX LT. unfold vad_FP, vtab_W. rewrite (vad_vlan_add_app t max p vid HEX LT). cbn [snd].
rewrite length_app. cbn [length]. unfold seg_spec.RVLAN_SIZE.
replace (length t <? length t + 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
cbn [app]. f_equal. f_equal. lia.
Qed.
Lemma vad_E_app : existsb (vad_match vid p) t = false -> L < max ->
forall a, vad_E a <-> (VD <= a < VD + 18 \/ n <= a < n + 4).
Proof using.
intros HEX LT a. unfold vad_E, vtab_E. rewrite (vad_vlan_add_app t max p vid HEX LT). cbn [snd].
rewrite length_app. cbn [length]. unfold seg_spec.RVLAN_SIZE.
replace (length t <? length t + 1)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
replace (Z.of_nat (length t + 1)) with (L + 1) by lia. split; intros [H|H]; [left; lia | right; exact H | left; lia | right; exact H].
Qed.
Lemma vad_awr_tab : forall a, existsb (vad_match vid p) t = false -> L < max ->
VD <= a < VD + 18 ->
awr_byte SEGS B VAD_STK sp0 vad_FP (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a.
Proof using HADD.
intros a HEX LT Ha. pose proof HADD as ((_ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _) & _).
pose proof (req_size_pos0 m ltac:(unfold seg_spec.RVLAN_SIZE in *; lia)) as [_ Hreq].
right; left. split.
- rewrite (vad_FP_app HEX LT). exists (VD, VD + 18). split; [left; reflexivity | cbn [fst snd]; lia].
- exists b, m. split; [exact Hbm|]. unfold seg_spec.RVLAN_SIZE in *. lia.
Qed.
Lemma vad_awr_n : forall a, existsb (vad_match vid p) t = false -> L < max -> n <= a < n + 4 ->
awr_byte SEGS B VAD_STK sp0 vad_FP (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a.
Proof using HADD.
intros a HEX LT Ha. pose proof HADD as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDST & _) & _).
assert (HF : inFP vad_FP a) by (rewrite (vad_FP_app HEX LT); exists (n, n + 4); split; [right; left; reflexivity | cbn [fst snd]; lia]).
destruct HDST as [((cid & pos & Hin & Hcid & Hf1 & Hf2) & _) | [((b & m & Hbm & Hb1 & Hb2) & _) | (Hs1 & Hs2 & _)]].
- right; right; right; right. right; right. split; [exact HF|]. exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- pose proof (req_size_pos0 m ltac:(lia)) as [_ Hreq].
  right; left. split; [exact HF|]. exists b, m. split; [exact Hbm|]. lia.
- right; right; right; right. right; left. split; [exact HF|]. lia.
Qed.

End w.
End e.
End d.
End b.
