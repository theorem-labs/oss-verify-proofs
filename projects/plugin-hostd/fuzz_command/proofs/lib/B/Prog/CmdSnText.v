(* The lemmas that the B walks' calls of the snprintf wrapper share (fuzz_command.asan-ubsan): the text of "%d",
   the format's bytes, the written part of snprintf, RtPFCmd.v's read-only words, the seed of the two shadow
   stores before the call, and the 32-aligned frame base of the functions that hold the buffer. They are about no
   single walk, so they are here once and the walks import them.

   Moved here with their proofs unchanged (the copies differ only in their name prefix):
   - snt_pf_dec .. snt_cr_disj: the B sup_add walk,
     lib/B/Prog/sup_add_sn.v:59-131 (prefix sas_), copied with prefix scb_ in an earlier version of
     lib/B/Prog/sup_call_b.v:56-126. snt_cr_low, snt_cr_in and snt_cr_disj state the bound 0x606000 (CMD_IMG_HI)
     where the copies state 0x30000: RtPFCmd's CMD_SNP_CR became CMD_CR's body, the image's two non-writable load
     segments, which end at 0xa5000.
   - snt_b_shadow, snt_E: sup_add_s3.v:49 sas3_shadow and :61 sas3_E (scb_E in sup_call_b.v:179).
   - snt_fmt_d: sup_call_b.v:265 scb_fmt_d. sup_add_s3.v:98 sas3_fmt_d states the same fact at its walk's
     constant SA_FMT_D (sup_add_s0.v:67, = 0x21f40), so it is snt_fmt_d up to conversion.
   - snt_sp1_facts, snt_land_m32, snt_denot_and_m32, snt_zr_apart: sup_add_s1a.v:103, :111, :119, :158 (prefix s1_),
     copied without prefix in an earlier version of sup_call_s1.v:143, :151, :159, :212 (the A sup_resp
     template's helpers for `andi sp,sp,-32`).
   *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdObj.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

(* ---- the texts ---- *)
(* printf_facts_c's %d text, as bytes, is RecFacts' dec: lib/Prog/RecAns.v pf_resp's steps without "resp " *)
Lemma snt_pf_dec : forall v, -2 ^ 31 <= v < 2 ^ 31 -> PF.pf_bytes (PF.pf_dec v) = dec v.
Proof.
intros c Hc. unfold PF.pf_dec, dec. unfold PF.pf_bytes.
assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
destruct (Z.ltb_spec c 0) as [N|N].
- cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
  exact (RA.pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
- cbn [app]. replace (Z.abs c) with c by lia.
  exact (RA.pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.
Lemma snt_text_d : forall v, PF.pf_text [PF.Pd] [PF.AInt v] = Some (PF.pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma snt_parse_d : PF.pf_parse [37; 100] = Some [PF.Pd].
Proof. reflexivity. Qed.

(* the reader's value at a byte is a byte *)
Lemma snt_aview_range : forall (segs : list Segment) H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof. intros segs H mem a v E. destruct (aview_byte segs H mem a v E) as (_ & _ & _ & Hr). exact Hr. Qed.
(* the text the wrapper writes, read back as the C string of its bytes *)
Lemma snt_astr_of_text : forall (segs : list Segment) H mem d (T : list Z) s,
  PF.pf_bytes T = s -> ~ In (Z_to_bv 8 0) s ->
  (forall i, 0 <= i <= Z.of_nat (length T) -> aview segs H mem (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
  astr_atR (aview segs H mem) d s.
Proof.
intros segs H mem d T s HTs Hno HB. split; [|exact Hno].
intros i Hi. subst s. unfold PF.pf_bytes in Hi |- *.
rewrite length_app, length_map in Hi. cbn [length] in Hi.
pose proof (HB (Z.of_nat i) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. rewrite Hb.
pose proof (snt_aview_range segs H mem _ _ Hb) as Hr.
f_equal.
replace (map (Z_to_bv 8) T ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (T ++ [0])) by (rewrite map_app; reflexivity).
rewrite (map_nth (Z_to_bv 8) (T ++ [0]) 0 i).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact Hr.
Qed.
(* a literal of CmdRo.v as the format's bytes *)
Lemma snt_nth_unsigned : forall (l : list byte) k, (k < length l)%nat ->
  nth k (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof. induction l as [|b l IH]; intros [|k] Hk; cbn [length nth map] in *; [lia | lia | reflexivity | apply IH; lia]. Qed.
Lemma snt_fmt_bytes : forall (rd : reader) f (lit : list byte) (fmt : list Z),
  abytes_atR rd f lit -> map (fun b : byte => bv_unsigned b) lit = fmt ++ [0] ->
  forall i, 0 <= i <= Z.of_nat (length fmt) -> rd (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0).
Proof.
intros rd f lit fmt H E i Hi.
assert (Hl : length lit = S (length fmt)).
{ apply (f_equal (@length Z)) in E. rewrite length_map, length_app in E. cbn [length] in E. lia. }
pose proof (H (Z.to_nat i) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal.
rewrite <- E, snt_nth_unsigned by lia. reflexivity.
Qed.
(* the written part of snprintf when the text and its terminator fit in the size *)
Lemma snt_sn_fit : forall n (T : list Z), Z.of_nat (length T) + 1 <= n ->
  sn_len (n - 1) T = Z.of_nat (length T) + 1 /\ sn_bytes (n - 1) T = T ++ [0].
Proof.
intros n T H. unfold sn_len, sn_bytes. rewrite firstn_all2 by lia.
split; [rewrite length_app; cbn [length]; lia | reflexivity].
Qed.

(* ---- RtPFCmd.v's read-only list CMD_SNP_CR: since two earlier commits CMD_CR's body, the image's two
   non-writable load segments [0x10000, 0x33000) and [0x33000, 0xa5000); below 0x606000 (CMD_IMG_HI, RtPFCmd.v:60, the
   image hull), so apart from the stack and the side-stack frames (RtPFDog.pa_frame_above_img: CMD_IMG_HI <= a frame
   of S). The bound is the literal, so a call site's numeric bounds close the premise by lia, as with 0x30000 before *)
Lemma snt_cr_low : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 0x606000)) CMD_SNP_CR = true.
Proof. vm_compute. reflexivity. Qed.
Lemma snt_cr_in : forall r, In r CMD_SNP_CR -> 0 <= fst r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) snt_cr_low r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma snt_cr_bounds : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) CMD_SNP_CR.
Proof. apply Forall_forall. intros r Hr. pose proof (snt_cr_in r Hr). lia. Qed.
Lemma snt_cr_disj : forall rs, Forall (fun q => 0x606000 <= fst q) rs ->
  Forall (fun r => Forall (zdisjoint r) rs) CMD_SNP_CR.
Proof.
intros rs Hrs. apply Forall_forall. intros r Hr. destruct (snt_cr_in r Hr) as [Hb1 Hb2].
apply Forall_forall. intros q Hq. pose proof (proj1 (Forall_forall _ _) Hrs q Hq) as Hq0. cbv beta in Hq0.
unfold zdisjoint. left. clear - Hb2 Hq0. lia.
Qed.

(* ---- the seed of the two shadow stores before the call ---- *)
(* one region: the 16 shadow bytes of a class-1 frame at the atom of s9 (25), of which a run may write the two of
   b = F + 32 (offsets 4 and 5): the state sup_add_s3.v seeds before its two `sb zero` stores *)
Definition snt_b_shadow : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 4 6 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
(* the environment of a seed: every register its own atom, no extra atom *)
Definition snt_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).

Section e.
Hypothesis VOBJS : cmd_val_objs.
(* the image atom of "%d" (A_OBJ 51 = 0x21f40) *)
Lemma snt_fmt_d : forall E, img_env VAL A_LIM E -> ew E 292 = w64 0x21f40.
Proof using VOBJS.
intros E HEI. rewrite <- (Z_to_bv_bv_unsigned _ (ew E 292)).
rewrite (HEI 292%nat ltac:(split; [unfold A_TEXT; lia | apply Nat.ltb_lt; vm_compute; reflexivity])).
change 292%nat with (A_OBJ 51%nat). rewrite (VOBJS 51%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. reflexivity.
Qed.
End e.
End f.
End d.

(* ---- the 32-aligned frame base: `andi sp,sp,-32` on a 16-aligned sp, as a value and as the symbolic denotation ---- *)
Lemma snt_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma snt_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma snt_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite snt_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* two ranges of which neither holds a byte of the other are apart *)
Lemma snt_zr_apart : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
(forall a, lo1 <= a < hi1 -> ~ (lo2 <= a < hi2)) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof. intros lo1 hi1 lo2 hi2 H1 H2 H. destruct (Z_le_gt_dec hi1 lo2); [left; exact l|]. right.
destruct (Z_le_gt_dec hi2 lo1); [exact l|]. exfalso. apply (H (Z.max lo1 lo2)); lia. Qed.
