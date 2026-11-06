(* check_words_pin_set on the ASan build of plugin-hostd/fuzz_command: the walk that proves its contract
   tcwps_spec (check_words_pin_set_c.v), in the style of cgif_file_fuzzer's cmpPixel walk (lib/A/AChd.v): an entry
   seed, symbolic runs by the verified executor (paj_run_tok), data-dependent branches split by psrr_branch_tok,
   the two wrapper calls composed into the journal through PaArtStr.v (PaArt.v's aj_art_at), and the return through paj_ret_at.

   The function (entry BASE + 0x2b3c = 0x89020, 58 instructions): if r < 5 the expected verdict is the literal
   "-" (0x21ac0); otherwise it is words[4] (loaded through an inline check at wp + 32), advanced by 8 when
   strncmp(words[4], "verdict=", 8) is 0. It then checks the recorded call's argument count (an inline check at
   cp + 4, must be 4) and its fourth argument (an inline check at cp + 32), compares that argument with the
   verdict by strcmp, and aborts when either differs. The pre-condition (nargs = 4, x3 = pin_verdict r w4) makes
   both abort edges unreachable, which the walk shows at each branch.

   Section hypotheses: the two wrapper contracts (RtString.v), the allocator record's laws and constants
   (AR_laws, PALib), and the record/image facts named below, each discharged by the instance or the record. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdAddr CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaArt PaArtStr PaNoChain PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_pin_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Notation PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_pin_set_c.pin_verdict.

(* The model side: strncmp(w, "verdict=", 8) is 0 exactly when w starts with "verdict=" (copied from the released
   plain proof's lib/Prog/CommandTac.v:60-118, which this file does not import: that module needs the plain image). *)
Lemma cw_notin_cons : forall b l, ~ In NUL (b :: l) -> bv_unsigned b <> 0 /\ ~ In NUL l.
Proof.
intros b l H. split.
- intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
- intros Hi. apply H. right. exact Hi.
Qed.
Lemma cw_walk_prefix : forall k s, ~ In NUL s -> ~ In NUL k -> k <> [] ->
exists v, strncmp_walk (s ++ [NUL]) (k ++ [NUL]) (length k - 1) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
induction k as [|c k IH]; intros s Hs Hk Hne; [congruence|].
destruct (cw_notin_cons c k Hk) as [Hc Hk'].
destruct s as [|a s'].
- cbn [app strncmp_walk]. unfold NUL. rewrite Z_to_bv_unsigned. cbn [bv_wrap].
eexists. split; [reflexivity|]. split; [intros E; exfalso; change (bv_wrap 8 0) with 0 in E; lia | intros E; discriminate].
- destruct (cw_notin_cons a s' Hs) as [Ha Hs'].
cbn [app length].
destruct k as [|c2 k2].
+ cbn [strncmp_walk Nat.sub Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
cbn [orb]. replace (0 - 0)%nat with 0%nat by reflexivity.
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
* eexists. split; [reflexivity|]. split; [intros _; cbn; f_equal; apply bv_eq; exact E | intros _; lia].
* eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E; subst; lia].
+ replace (S (length (c2 :: k2)) - 1)%nat with (S (length (c2 :: k2) - 1)) by (cbn; lia).
cbn [strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
cbn [orb Nat.eqb].
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
* destruct (IH s' Hs' Hk' ltac:(discriminate)) as (v & Hw & Hv).
exists v. split; [exact Hw|]. rewrite Hv. cbn [firstn length].
replace a with c by (apply bv_eq; symmetry; exact E).
split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
* eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E1 _; subst; lia].
Qed.
Lemma cw_strncmp_prefix : forall s k, ~ In NUL s -> ~ In NUL k -> k <> [] ->
exists v, strncmp_model (s ++ [NUL]) (k ++ [NUL]) (Z.of_nat (length k)) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
intros s k Hs Hk Hne. unfold strncmp_model.
destruct k as [|c k']; [congruence|].
replace (Z.of_nat (length (c :: k')) =? 0) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
replace (Z.to_nat (Z.of_nat (length (c :: k')) - 1)) with (length (c :: k') - 1)%nat by lia.
apply cw_walk_prefix; assumption.
Qed.
Lemma cw_prefixb_iff : forall s k, prefixb s k = true <-> firstn (length k) s = k.
Proof.
intros s k. unfold prefixb, bytes_eqb.
destruct (list_eq_dec Z.eq_dec _ _) as [E|NE].
- split; [intros _; apply map_unsigned_inj; exact E | reflexivity].
- split; [discriminate | intros H; exfalso; apply NE; rewrite H; reflexivity].
Qed.
Lemma cw_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
induction l as [|x l IH]; intros k i d.
- destruct k; cbn; destruct i; reflexivity.
- destruct k as [|k]; cbn; [reflexivity | apply IH].
Qed.
Lemma cw_notin0 : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate. Qed.
Lemma cw_in_of_existsb : forall e l, existsb (Z.eqb e) l = true -> In e l.
Proof. intros e l H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He. subst. exact Hx. Qed.
Lemma cw_agree32 : forall E1 E0 E, env_agree 32 E1 E0 -> env_agree 40 E0 E -> env_agree 32 E1 E.
Proof. intros E1 E0 E [A1 D1] [A2 D2]. split; [intros n Hn; rewrite A2 by lia; apply A1; lia | congruence]. Qed.
Lemma cw_ew_agree : forall k E0 E n, env_agree k E0 E -> (n < k)%nat -> ew E n = ew E0 n.
Proof. intros k E0 E n [HA _] Hn. exact (HA n Hn). Qed.
Lemma cw_U_atom : forall E0 E n c v, env_agree 40 E0 E -> (n < 40)%nat -> ew E0 n = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
intros E0 E n c v HA Hn Hv R1 R2. rewrite U_SOff, (cw_ew_agree 40 E0 E n HA Hn), Hv, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma cw_lt_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v <? z).
Proof.
intros E n v z Hn Hv Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cw_sel_U : forall E n m p v, U E (SOff n 0) = p -> U E (SOff m 0) = v -> 0 <= p -> p + 8 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff m 0) (SLit 1)) (SLit 3))) = p + (if v =? 0 then 8 else 0).
Proof.
intros E n m p v Hp Hv R1 R2. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Hp, Hv, !U_SLit.
pose proof (U_range E (SOff m 0)) as RV. rewrite Hv in RV. unfold M64 in RV.
assert (Hs : zcanon (Z.shiftl (zcanon (if v <? zcanon 1 then 1 else 0)) (Z.land (zcanon 3) 63)) = if v =? 0 then 8 else 0).
{ destruct (Z.eqb_spec v 0) as [->|Hne]; [reflexivity|].
replace (v <? zcanon 1) with false by (symmetry; apply Z.ltb_ge; change (zcanon 1) with 1; lia).
reflexivity. }
rewrite Hs. unfold zcanon, M64. apply Z.mod_small. destruct (v =? 0); lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* The entry seed. Atoms: the registers (0..31), the shadow base SB (32), the recorded fourth argument p3 (33) and
   words[4]'s pointer p4 (34). Regions: the 32-byte frame, the GOT word and the shadow-base cell, the recorded
   call's two fields (nargs = 4 and the fourth argument) and, when r >= 5, the slot words[4]. Shadow entries: the
   recorded call (inside g_rec, zero shadow) and, when r >= 5, the slot. *)
Definition CBx : sv := SOff 32 0.
Definition CBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cw_call : YP09.region :=
YP09.mkRegion (Some 10%nat) 4 40 0 0 [YP09.mkChunk 4 (CVal 4 (SLit 4)); YP09.mkChunk 32 (CVal 8 (SOff 33 0))].
Definition cw_words : YP09.region := YP09.mkRegion (Some 11%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 34 0))].
Definition cw_regions (hi : bool) : smem :=
[stack_region 32; got_regionP; bcell_regionP 32; cw_call] ++ (if hi then [cw_words] else []).
Definition cw_facts (hi : bool) : facts :=
mkFacts ([ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (A_G_REC + OFF_CALLS) (A_G_REC + REC_SIZE - CALL_SIZE) 0);
(12%nat, mkAF 0 64 0); (32%nat, mkAF SB SB 0) ] ++ (if hi then [(11%nat, mkAF 4064 (140737479966720 - 40) 0)] else [])) [] [].
Definition ss_cw (hi : bool) : sstate := mkSS AF_check_words_pin_set sr_atoms (cw_regions hi) None (cw_facts hi).
Definition cw_SH (hi : bool) : list shent := mkSHE 10 0 40 :: (if hi then [mkSHE 11 32 40] else []).
Definition cw_extra (p3 p4 : Z) : list word := map (Z_to_bv 64) [SB; p3; p4].
Definition EC (regs : bvmap 5 word) (p3 p4 : Z) : env := Eimg (Ereg regs (cw_extra p3 p4)).
(* the memory outside this call's stack window is the entry memory *)
Definition kept (W : world SEGS) (mem m : word -> option byte) (sp0 : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - CWPS_STK <= a < sp0) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
(* a string a wrapper may read, at the entry memory *)
Definition sready (W : world SEGS) (mem : word -> option byte) (p : Z) (s : list byte) : Prop :=
0 < p /\ p + Z.of_nat (length s) + 1 <= alloc_ceiling /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
astr_atR (aview SEGS (w_H W) mem) p s /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) p (Z.of_nat (length s) + 1) /\
amem_range p (Z.of_nat (length s) + 1) /\
atail_vis SEGS W mem (p + Z.of_nat (length s)).
Definition wr_only_stack (rs : smem) : bool :=
forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
(match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end && (-32 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0))) rs.

Lemma not_wrange_stack : forall E rs a, wr_only_stack rs = true ->
~ (bv_unsigned (ew E 2) - 32 <= a < bv_unsigned (ew E 2)) -> ~ in_wrange E rs a.
Proof.
intros E rs a Hw Ha (r & Hin & Hr). unfold wr_only_stack in Hw. rewrite forallb_forall in Hw. specialize (Hw r Hin).
apply orb_prop in Hw as [Hw | Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw Hhi]. apply andb_prop in Hw as [Hb Hlo]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
destruct (YP09.r_base r) as [n|] eqn:Eb; [|discriminate]. apply Nat.eqb_eq in Hb. subst n.
cbn [base_val] in Hr. lia.
Qed.
Lemma aview_frame_kept : forall E rs H (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hw. unfold aview, mbyte.
rewrite (Hf (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hw.
Qed.
Lemma kept_refl : forall W mem sp0, kept W mem mem sp0.
Proof. intros W mem sp0 a _ _. reflexivity. Qed.
Lemma kept_run : forall W mem m0 m1 E rs sp0, kept W mem m0 sp0 ->
frame_of E rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) -> wr_only_stack rs = true -> bv_unsigned (ew E 2) = sp0 ->
kept W mem m1 sp0.
Proof.
intros W mem m0 m1 E rs sp0 HK Hf Hw Hsp a Ha Hn. assert (ESTACK = 4096) as Hes by reflexivity.
rewrite (aview_frame_kept E rs (w_H W) m0 m1 a Hf Ha); [exact (HK a Ha Hn)|].
apply (not_wrange_stack E rs a Hw). rewrite Hsp. unfold CWPS_STK in Hn. lia.
Qed.
Lemma kept_call : forall W mem m0 m1 sp0 lo hi, kept W mem m0 sp0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ False -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
sp0 - CWPS_STK <= lo -> hi <= sp0 -> kept W mem m1 sp0.
Proof. intros W mem m0 m1 sp0 lo hi HK Hf Hlo Hhi a Ha Hn. rewrite (Hf a Ha); [exact (HK a Ha Hn) | lia | tauto]. Qed.
(* after PaDenot.v:76-86's region_kept_aview: a region's bytes are kept, and its writable range is present after *)
Lemma cw_region_kept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma val_mem_of_aval : forall H (mem : word -> option byte) a (n : nat) v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (shadow_mono x x' H1) as M1. pose proof (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma aread_ok_prefix : forall stk W regs mem x n n', aread_ok SEGS stk W regs mem x n -> 0 <= n' <= n ->
aread_ok SEGS stk W regs mem x n'.
Proof.
intros stk W regs mem x n n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hn.
split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|]. split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hp. apply (hull_sub _ x n x n'); [apply H6; lia | lia | lia | lia].
Qed.
Lemma sready_skipn : forall W mem p s k, sready W mem p s -> (k <= length s)%nat ->
sready W mem (p + Z.of_nat k) (skipn k s).
Proof.
intros W mem p s k (Hp & Hpn & Hn & [Hb Hnul] & Hra & Hhv & Ham & Htl) Hk.
unfold sready. rewrite skipn_length.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ split.
- intros i Hi. rewrite length_app, skipn_length in Hi. cbn [length] in Hi.
replace (skipn k s ++ [Z_to_bv 8 0]) with (skipn k (s ++ [Z_to_bv 8 0])) by (rewrite skipn_app; replace (k - length s)%nat with 0%nat by lia; reflexivity).
rewrite cw_nth_skipn. replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia.
apply Hb. rewrite length_app. cbn [length]. lia.
- intros Hi. apply Hnul. rewrite <- (firstn_skipn k s). apply in_or_app. right. exact Hi. }
split; [eapply range_addressable_sub; [exact Hra | lia | lia]|].
split; [apply (hull_sub _ p (Z.of_nat (length s) + 1)); [exact Hhv | lia | lia | lia]|].
split; [unfold amem_range in *; lia|].
replace (p + Z.of_nat k + Z.of_nat (length s - k)) with (p + Z.of_nat (length s)) by lia. exact Htl.
Qed.
Lemma sready_call : forall W mem memT p s sp0 regsT,
sready W mem p s -> alloc_ceiling <= sp0 - CWPS_STK -> kept W mem memT sp0 ->
(forall a, sp0 - CWPS_STK <= a < sp0 -> apresent (w_H W) memT a) ->
sp0 - CWPS_STK <= spZ regsT - 2 * ESTACK ->
0 < p /\ astr_at SEGS W memT p s /\ aread_ok SEGS (2 * ESTACK) W regsT memT p (astr_len s + 1) /\
atail_vis SEGS W memT (p + astr_len s).
Proof.
intros W mem memT p s sp0 regsT (Hp & Hpn & Hn32 & [Hb Hnul] & Hra & Hhv & Ham & Htl) Hce HK Hpr Hsp. unfold kept in HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (ESTACK = 4096) as Hes by reflexivity.
unfold astr_len.
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memT a = aview SEGS (w_H W) mem a)
by (intros a Ha; apply HK; lia).
assert (HB : abytes_at SEGS W memT p (s ++ [Z_to_bv 8 0])).
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KEEP by lia. apply Hb. rewrite length_app. cbn [length]. lia. }
split; [exact Hp|]. split; [split; [exact HB | exact Hnul]|]. split.
- unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split.
- replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (HB (Z.to_nat (a - p))) by (rewrite length_app; cbn [length]; lia). discriminate.
- unfold ascratch_stk. lia. }
split; [exact Ham|]. split.
{ intros x Hx. destruct (Hra x Hx) as (sh & Hsh & Hok). exists sh. split; [|exact Hok].
rewrite KEEP; [exact Hsh|]. unfold shadow_of_addr, SHADOW_OFF in *. lia. }
{ intros _ s0 Hs0. rewrite KEEP; [exact (Hhv s0 Hs0)|]. unfold shadow_addr, SHADOW_OFF in Hs0. lia. }
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - CWPS_STK)) as [Hlt|Hge].
+ rewrite (HK a ltac:(lia) ltac:(lia)). exact (Htl a Ha).
+ pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as M8.
apply (aview_some_of_apresent SEGS). apply Hpr. unfold CWPS_STK in *. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : astrncmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the record: g_rec lies inside one of its zero-shadow ranges *)
Hypothesis GREC_ZS : Exists (fun z => fst z <= A_G_REC /\ A_G_REC + REC_SIZE <= fst z + snd z) (as_zero_shadow B).
(* the record and AR: a live block's last 8-byte word is readable (req_size is a multiple of 8) *)
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + req_size n -> atail_vis SEGS W mem e.
(* the record and AR: the shadow of the two literals ("-" and "verdict=", ASan globals with redzones) *)
Hypothesis cw_lit_shadow : forall ly S W mem md a n, AR SEGS B ly S W mem md -> In (a, n) [(0x21ac0, 2); (0x21b60, 9)] ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Lemma grec_ra : forall ly S W mem md, AR SEGS B ly S W mem md ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_G_REC REC_SIZE.
Proof.
intros ly S W mem md HAR.
apply Exists_exists in GREC_ZS as (z & Hz & Hlo & Hhi).
assert (Hin : In z (zero_shadow_ranges B ly)) by (right; exact Hz).
pose proof (al_zshadow _ _ LAWS ly S W mem md z HAR Hin) as Hzs.
destruct (zshadow_range_facts B ly S _ z (proj1 HAR) Hin) as (Hal & H0 & Hl & _).
assert (RA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fst z) (snd z / 8 * 8)).
{ apply zero_shadow_range; [exact Hal | rewrite Z.mod_mul by lia; reflexivity |].
intros i Hi. apply Hzs. rewrite Z.div_mul in Hi by lia. exact Hi. }
eapply range_addressable_sub; [exact RA | lia |].
unfold A_G_REC, REC_SIZE in *. pose proof (Z.div_mod (snd z) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd z) 8 ltac:(lia)).
pose proof (Z.div_mod (fst z) 8 ltac:(lia)). lia.
Qed.
Lemma cw_shok : forall (hi : bool) ly S W mem md E cp wp,
AR SEGS B ly S W mem md -> ew E 32 = Z_to_bv 64 SB -> ew E 10 = Z_to_bv 64 cp -> ew E 11 = Z_to_bv 64 wp ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
(hi = true -> in_blockA (ablocks B ly S) (wp + 32) 8 /\ 0 <= wp) ->
sh_ok SEGS CBx (cw_SH hi) E (mrestrict (w_H W) mem).
Proof.
intros hi ly S W mem md E cp wp HAR E32 E10 E11 Hc1 Hc2 Hw.
pose proof (grec_ra ly S W mem md HAR) as RG.
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in Hc1, Hc2, RG.
assert (UB : U E CBx = SHADOW_OFF) by (unfold CBx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (U10 : U E (SOff 10 0) = cp) by (apply U_atom; [exact E10 | lia]).
assert (G : shent_ok SEGS CBx E (mrestrict (w_H W) mem) (mkSHE 10 0 40)).
{ apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 0x5e3740 960 cp 0 40 RG UB U10); [lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia. }
unfold sh_ok, cw_SH. destruct hi.
- destruct (Hw eq_refl) as [(b & k & Hin & Hb & He) Hw0].
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & _ & _ & Hk).
pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk]. pose proof asan_consts as (C1 & _).
assert (U11 : U E (SOff 11 0) = wp) by (apply U_atom; [exact E11 | lia]).
constructor; [exact G|]. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 11 (wp + 32) 8 wp 32 40); [| exact UB | exact U11 | lia | lia |].
+ apply (range_addressable_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia].
+ intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- constructor; [exact G | constructor].
Qed.

Lemma cw_entry : forall (hi : bool) ly S W (regs : bvmap 5 word) mem md (cp wp r p3 p4 : Z),
afn_pre_na SEGS B CWPS_STK ly S W regs mem md -> cmd_val_objs ->
getr regs 10 = w64 cp -> getr regs 11 = w64 wp -> getr regs 12 = w64 r -> 0 <= r <= 64 ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW W mem) (cp + CALL_OFF_NARGS) 4 4 ->
aval_mem (rdW W mem) (cp + CALL_OFF_ARGS + 24) 8 p3 -> 0 <= p3 < 2 ^ 64 ->
(hi = true -> in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64) ->
st_ok_pi SEGS VAL (EC regs p3 p4) (ss_cw hi)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_words_pin_set)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx (cw_SH hi) (EC regs p3 p4) (mrestrict (w_H W) mem).
Proof.
intros hi ly S W regs mem md cp wp r p3 p4 HPRE HOBJ H10 H11 H12 Hr Hc1 Hc2 Hna Hp3 Rp3 Hw.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CWPS_STK = 8224) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in Hc1, Hc2.
rewrite restrict_mkst_fx.
set (E := EC regs p3 p4).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cw_extra p3 p4)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 wp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 p4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B10 : base_val E (Some 10%nat) = cp) by (apply VB; [exact E10 | lia]).
assert (B241 : base_val E (Some (A_OBJ 0)) = 0xa63f0) by (rewrite <- V0; apply VB; [exact E241 | pose proof (pa_val_range (A_OBJ 0)); lia]).
assert (B253 : base_val E (Some (A_OBJ 12)) = 0xb10b8) by (rewrite <- V12; apply VB; [exact E253 | pose proof (pa_val_range (A_OBJ 12)); lia]).
assert (B2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (RS : region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 32)).
{ unfold stack_region, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B2.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RG : region_ok SEGS E (mrestrict (w_H W) mem) got_regionP).
{ unfold got_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite <- V0, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot). }
assert (RB : region_ok SEGS E (mrestrict (w_H W) mem) (bcell_regionP 32)).
{ unfold bcell_regionP, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite <- V12, Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RC : region_ok SEGS E (mrestrict (w_H W) mem) cw_call).
{ unfold cw_call, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val SEGS E _ cp 4 4 (SLit 4) 4); [cbn [sv_denot]; reflexivity | zside | zside |].
exact (val_mem_of_aval _ _ _ _ _ Hna).
- apply (chunk_ok_val SEGS E _ cp 32 8 (SOff 33 0) p3); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
replace (cp + 32) with (cp + CALL_OFF_ARGS + 24) by (unfold CALL_OFF_ARGS; lia). exact (val_mem_of_aval _ _ _ _ _ Hp3). }
assert (FACT0 : forall l, atoms_ok E l ->
facts_ok E (mkFacts ([ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF (A_G_REC + OFF_CALLS) (A_G_REC + REC_SIZE - CALL_SIZE) 0);
(12%nat, mkAF 0 64 0); (32%nat, mkAF SB SB 0) ] ++ l) [] [])).
{ intros l Hl. split; [|split; [exact I | exact I]].
cbn [f_atoms app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E12, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE.
split; [repeat split; lia|]. split; [repeat split; lia|]. split; [repeat split; lia|]. split; [repeat split; lia|]. exact Hl. }
destruct hi.
- destruct (Hw eq_refl) as ((b & k & Hin & Hb & He) & Hwm & Rp4).
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & _ & _ & Hk).
pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
pose proof (blk_off_imgP B ly S W mem md b k HAR Hin) as Hoff. unfold off_img in Hoff.
assert (B11 : base_val E (Some 11%nat) = wp) by (apply VB; [exact E11 | lia]).
split.
+ unfold ss_cw. apply pa_entry_st_ok_full.
* apply regs_ok_Eimg_Ereg.
* vm_compute. reflexivity.
* unfold cw_regions. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; try assumption.
unfold cw_words, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite B11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ wp 32 8 (SOff 34 0) p4); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_of_aval _ _ _ _ _ Hwm).
* apply pairwise_disjoint_of_extents. unfold cw_regions, cw_call, cw_words, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B10, B11, B241, B253.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hceil H47 Hshi Hc1 Hc2 Hb Hb4096 He Hbceil Hrk Hoff C1 WS Hstk0. clear. intros.
repeat split; lia.
* apply FACT0. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E11, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
+ apply (cw_shok true ly S W mem md E cp wp HAR E32 E10 E11); [unfold A_G_REC, OFF_CALLS; lia | unfold A_G_REC, CALL_SIZE, REC_SIZE; lia |].
intros _. split; [exists b, k; split; [exact Hin | split; [exact Hb | exact He]] | lia].
- split.
+ unfold ss_cw. apply pa_entry_st_ok_full.
* apply regs_ok_Eimg_Ereg.
* vm_compute. reflexivity.
* unfold cw_regions. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; assumption.
* apply pairwise_disjoint_of_extents. unfold cw_regions, cw_call, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B10, B241, B253.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hceil H47 Hshi Hc1 Hc2 C1 WS Hstk0. clear. intros.
repeat split; lia.
* apply FACT0. exact I.
+ apply (cw_shok false ly S W mem md E cp wp HAR E32 E10 E11); [unfold A_G_REC, OFF_CALLS; lia | unfold A_G_REC, CALL_SIZE, REC_SIZE; lia |].
intros X. discriminate X.
Qed.

Lemma sready_of_blk : forall ly S W mem md p s,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) p (Z.of_nat (length s) + 1) -> astr_atR (rdW W mem) p s ->
sready W mem p s.
Proof.
intros ly S W mem md p s HAR (b & k & Hin & Hb & He) Hstr.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _ & Hk).
pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
unfold sready. split; [lia|]. split; [lia|]. split; [unfold MALLOC_MAX in Hk; lia|]. split; [exact Hstr|]. split.
{ apply (range_addressable_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia]. }
split. { apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia | lia]. }
split. { apply (amem_range_of_block SEGS B LAWS ly S W mem md b k); [exact HAR | exact Hin | lia | lia]. }
apply (cmd_heap_tail_vis ly S W mem md b k); [exact HAR | exact Hin | lia].
Qed.
Lemma sready_lits : forall ly S W mem md, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
sready W mem 0x21ac0 S_DASH /\ sready W mem 0x21b60 S_VERDICT.
Proof.
intros ly S W mem md HAR [HB HT].
destruct (cw_lit_shadow ly S W mem md 0x21ac0 2 HAR ltac:(left; reflexivity)) as [RA1 HV1].
destruct (cw_lit_shadow ly S W mem md 0x21b60 9 HAR ltac:(right; left; reflexivity)) as [RA2 HV2].
unfold cmd_ro_bytes in HB.
repeat match type of HB with _ /\ _ => let H := fresh "Hb" in destruct HB as [H HB] end.
pose proof asan_consts as (C1 & _).
split.
- unfold sready. change (Z.of_nat (length S_DASH)) with 1. split; [lia|]. split; [lia|]. split; [lia|].
split; [split; [|apply cw_notin0; vm_compute; reflexivity]; match goal with H : abytes_atR _ 0x21ac0 _ |- _ => exact H end|].
split; [exact RA1|]. split; [exact HV1|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
intros a Ha. apply (HT (0x21ac0 + 1)); [apply cw_in_of_existsb; vm_compute; reflexivity | exact Ha].
- unfold sready. change (Z.of_nat (length S_VERDICT)) with 8. split; [lia|]. split; [lia|]. split; [lia|].
split; [split; [|apply cw_notin0; vm_compute; reflexivity]; match goal with H : abytes_atR _ 0x21b60 _ |- _ => exact H end|].
split; [exact RA2|]. split; [exact HV2|]. split; [unfold amem_range, kLowMemEnd; left; lia|].
intros a Ha. apply (HT (0x21b60 + 8)); [apply cw_in_of_existsb; vm_compute; reflexivity | exact Ha].
Qed.
Lemma rom_view_call : forall W mem memT sp0, arodata_okP SEGS RLO RHI B (rdW W mem) ->
alloc_ceiling <= sp0 - CWPS_STK -> kept W mem memT sp0 -> rt_rom_view SEGS B W memT.
Proof.
intros W mem memT sp0 HRO Hce HK a Ha Ho He. unfold kept in HK.
assert (Himg : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as Hr. pose proof asan_consts as (C1 & _).
rewrite HK by lia. apply HRO; [left; exact Ha | exact Ho | exact He].
Qed.
Lemma aj_pres : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof. intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres. Qed.
(* the two wrapper calls of the walk, with the wrappers' premises discharged from the strings' entry readiness *)
Lemma cw_strncmp_at : forall ly S W regs mem md (ms : machine_state) md' p4 w4,
ajournal SEGS B CWPS_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> alloc_ceiling <= spZ regs - CWPS_STK -> kept W mem (ms_mem ms) (spZ regs) ->
getr (ms_regs ms) 10 = w64 p4 -> getr (ms_regs ms) 11 = w64 0x21b60 -> getr (ms_regs ms) 12 = w64 8 ->
spZ (ms_regs ms) = spZ regs - 32 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 11156) ->
sready W mem p4 w4 -> amem_range p4 (astr_len w4 + 8) -> sready W mem 0x21b60 S_VERDICT ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strncmp)) (ms_mem ms) (seg_rom SEGS)) md')
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 11156)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CWPS_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved (ms_regs ms) regs2 /\
(getr regs2 10 = w64 0 <-> strncmp_model (w4 ++ [Z_to_bv 8 0]) (S_VERDICT ++ [Z_to_bv 8 0]) 8 = Some 0) /\
kept W mem mem2 (spZ regs) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -32 - 2 * ESTACK <= a < spZ regs + -32) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)).
Proof.
intros ly S W regs mem md ms md' p4 w4 HJ HRO HCE HK Ha0 Ha1 Ha2 Hsp Hgp Htp Hra RX MX RY.
(* the literal "verdict=" (8 bytes) lies in the image's .rodata, in the low band *)
assert (MY : amem_range 0x21b60 (astr_len S_VERDICT + 8)).
{ apply amem8_of_low; [lia|]. assert (LV : astr_len S_VERDICT = 8) by reflexivity. rewrite LV. unfold kLowMemEnd. lia. }
pose proof (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpr.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (sready_call W mem (ms_mem ms) p4 w4 (spZ regs) (ms_regs ms) RX HCE HK Hpr ltac:(rewrite Hsp; unfold CWPS_STK; lia))
as (Hx0 & Hsx & Hrx & Htx).
destruct (sready_call W mem (ms_mem ms) 0x21b60 S_VERDICT (spZ regs) (ms_regs ms) RY HCE HK Hpr ltac:(rewrite Hsp; unfold CWPS_STK; lia))
as (Hy0 & Hsy & Hry & Hty).
eapply SRr_mono.
{ apply (aj_strncmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIGMA CS___interceptor_trampoline_strncmp) ASTRNCMP W (ms_regs ms) (ms_mem ms)
CWPS_STK (spZ regs) [] ly S W mem md [] ly S md' 0 p4 0x21b60 8 w4 S_VERDICT (-32) (Z_to_bv 64 (BASE + 11156)) HJ Ha0 Ha1 Ha2
ltac:(lia) Hx0 Hy0); try assumption.
all: first [ rewrite Hsp; lia | reflexivity | lia | (unfold CWPS_STK; lia) | (apply ret_ok_codeptr_v; [lia | reflexivity])
| (apply (aread_ok_prefix _ _ _ _ _ _ _ Hrx); unfold astr_len; lia) | (apply (aread_ok_prefix _ _ _ _ _ _ _ Hry); unfold astr_len; lia)
| exact (rom_view_call W mem (ms_mem ms) (spZ regs) HRO HCE HK) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hcmp|].
split; [apply (kept_call W mem (ms_mem ms) mem2 (spZ regs) (spZ regs + -32 - 2 * ESTACK) (spZ regs + -32) HK Hfr); unfold CWPS_STK; lia|].
exact Hfr.
Qed.
Lemma cw_strcmp_at : forall ly S W regs mem md (ms : machine_state) md' p3 x3 y sy,
ajournal SEGS B CWPS_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> alloc_ceiling <= spZ regs - CWPS_STK -> kept W mem (ms_mem ms) (spZ regs) ->
getr (ms_regs ms) 10 = w64 p3 -> getr (ms_regs ms) 11 = w64 y ->
spZ (ms_regs ms) = spZ regs - 32 -> getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 11240) ->
sready W mem p3 x3 -> sready W mem y sy ->
SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA CS___interceptor_trampoline_strcmp)) (ms_mem ms) (seg_rom SEGS)) md')
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 11240)) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CWPS_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved (ms_regs ms) regs2 /\ (getr regs2 10 = w64 0 <-> x3 = sy) /\
kept W mem mem2 (spZ regs) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -32 - 2 * ESTACK <= a < spZ regs + -32) -> ~ False ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a)).
Proof.
intros ly S W regs mem md ms md' p3 x3 y sy HJ HRO HCE HK Ha0 Ha1 Hsp Hgp Htp Hra RX RY.
pose proof (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hpr.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (sready_call W mem (ms_mem ms) p3 x3 (spZ regs) (ms_regs ms) RX HCE HK Hpr ltac:(rewrite Hsp; unfold CWPS_STK; lia))
as (Hx0 & Hsx & Hrx & Htx).
destruct (sready_call W mem (ms_mem ms) y sy (spZ regs) (ms_regs ms) RY HCE HK Hpr ltac:(rewrite Hsp; unfold CWPS_STK; lia))
as (Hy0 & Hsy & Hry & Hty).
eapply SRr_mono.
{ apply (aj_strcmp_at SEGS B LAWS pa_segs_low (pal_env B TL) (SIGMA CS___interceptor_trampoline_strcmp) ASTRCMP W (ms_regs ms) (ms_mem ms)
CWPS_STK (spZ regs) [] ly S W mem md [] ly S md' 0 p3 y x3 sy (-32) (Z_to_bv 64 (BASE + 11240)) HJ Ha0 Ha1 Hx0 Hy0); try assumption.
all: first [ rewrite Hsp; lia | reflexivity | lia | (unfold CWPS_STK; lia) | (apply ret_ok_codeptr_v; [lia | reflexivity])
| exact (rom_view_call W mem (ms_mem ms) (spZ regs) HRO HCE HK) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hcmp|].
split; [apply (kept_call W mem (ms_mem ms) mem2 (spZ regs) (spZ regs + -32 - 2 * ESTACK) (spZ regs + -32) HK Hfr); unfold CWPS_STK; lia|].
exact Hfr.
Qed.
Lemma cw_img_atom : forall E a, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> ew E a = Z_to_bv 64 (VAL a).
Proof. intros E a HE Ha. rewrite <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma cw_ne0_false : forall E n (w : word), ew E n = w -> w = w64 0 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E n w Hn Hw. rewrite branch_ne_U, U_SOff, U_SLit, Hn, Hw. reflexivity. Qed.
Lemma cw_havoc_a0 : forall E k (regs2 : bvmap 5 word), ew (havoc E k (map (getr regs2) CLOB)) (k + 4) = getr regs2 10.
Proof. intros E k regs2. rewrite (ew_havoc_new E k _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). reflexivity. Qed.

(* the walk's tactics: the stack pointer of the current environment, and the memory kept across a run *)
Ltac cw_usp := lazymatch goal with |- bv_unsigned (ew ?E 2) = _ =>
lazymatch goal with HAG : env_agree 40 ?E0 E, U0 : bv_unsigned (ew ?E0 2) = _ |- _ =>
first [exact U0 | rewrite (cw_ew_agree 40 E0 E 2 HAG ltac:(lia)); exact U0] end end.
Ltac cw_keep := lazymatch goal with
| HK : kept ?W ?mem ?m0 ?sp0, HFr : frame_of ?E ?rs (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
let HK2 := fresh "HK" in
pose proof (kept_run W mem m0 m1 E rs sp0 HK HFr ltac:(vm_compute; reflexivity) ltac:(cw_usp)) as HK2;
clear HK HFr; rename HK2 into HK end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac cw_run := lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CBspan; [awr_ok_tac; cw_usp |]; cw_keep end.
Ltac cw_base := first
[ eassumption
| lazymatch goal with HAG : env_agree 40 ?E0 ?E |- bv_unsigned (ew ?E ?n) = _ =>
rewrite (cw_ew_agree 40 E0 E n HAG ltac:(lia)); eassumption end
| lazymatch goal with HEI : img_env _ _ ?E |- bv_unsigned (ew ?E ?n) = _ =>
rewrite (HEI n ltac:(cbv; lia)); eassumption end ].
(* the regions after a wrapper call: the call wrote only below its own stack pointer *)
Ltac cw_kept_regions HS2 Hfr2 HJ2 :=
match type of HS2 with ?tt -> _ => let HRK := fresh "HRK" in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
(eapply cw_region_kept; [cw_base | intros a Ha; apply Hfr2; [lia | lia | tauto]
| intros a Ha; first [lia | apply (aj_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); unfold CWPS_STK; lia]]) |].
(* the return: the post-condition of the contract *)
Ltac cw_leaf := lazymatch goal with HS : st_ok_pi _ _ ?E _ (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
HAG : env_agree 40 ?E0 ?E, HAE : env_agree 32 _ ?E0, F1 : ew ?E0 1 = _, Hra : YK0s.ret_ok _ |- _ =>
eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
let R1 := fresh "R1" in prreg HS (1%bv : bv 5) R1;
unfold apost_base; eexists _, _, _, _, _;
split; [cbn [ms_regs]; rewrite R1, (cw_ew_agree 40 E0 E 1 HAG ltac:(lia)), F1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ _ _ HS); [exact (cw_agree32 _ _ _ HAE HAG) | vm_compute; reflexivity]|];
split; reflexivity end.

Theorem pb_check_words_pin_set : tcwps_spec B MT.
Proof.
unfold tcwps_spec.
intros ly S W regs mem md cp wp r nargs p4 p3 w4 x3 HPRE HRO HLIT HOBJ H10 H11 H12 Hr Hcp1 Hcp2 Hcp8 Hna Hna6 H3 H4 Hwp8 Hn4 Hx3 Hev.
clear Hcp8 Hwp8.
subst nargs.
destruct (H3 eq_refl) as (Hp3m & Rp3 & Hp3b & Hp3s). clear H3.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CWPS_STK = 8224) by reflexivity.
assert (HCE : alloc_ceiling <= spZ regs - CWPS_STK) by lia.
pose proof (sready_of_blk ly S W mem md p3 x3 HAR Hp3b Hp3s) as R3.
destruct (sready_lits ly S W mem md HAR HLIT) as [RDASH RVERD].
assert (V29 : VAL (A_OBJ 29) = 0x21ac0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V36 : VAL (A_OBJ 36) = 0x21b60) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
assert (HWH : (4 <? r) = true -> in_blockA (ablocks B ly S) (wp + 32) 8 /\ aval_mem (rdW W mem) (wp + 32) 8 p4 /\ 0 <= p4 < 2 ^ 64).
{ intros Hb. apply Z.ltb_lt in Hb. destruct (H4 Hb) as (Hwb & _ & Hwm & Rp4 & _). split; [exact Hwb | split; [exact Hwm | exact Rp4]]. }
destruct (cw_entry (4 <? r) ly S W regs mem md cp wp r p3 p4 HPRE HOBJ H10 H11 H12 Hr Hcp1 Hcp2 Hna Hp3m Rp3 HWH) as [HS SHOK].
pose proof (ajournal_init_na SEGS B CWPS_STK [] ly S W regs mem md HPRE) as HJ.
pose proof (kept_refl W mem (spZ regs)) as HK.
unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in Hcp1, Hcp2.
remember (EC regs p3 p4) as E0 eqn:HE0.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs (cw_extra p3 p4)) n)
by (intros n Hn; rewrite HE0; unfold EC; apply Eimg_low; exact Hn).
assert (F1 : ew E0 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (F3 : ew E0 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (F4 : ew E0 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (F2 : ew E0 2 = Z_to_bv 64 (spZ regs))
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (F10 : ew E0 10 = Z_to_bv 64 cp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (F11 : ew E0 11 = Z_to_bv 64 wp) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (F12 : ew E0 12 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (F32 : ew E0 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (F33 : ew E0 33 = Z_to_bv 64 p3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (F34 : ew E0 34 = Z_to_bv 64 p4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (cw_extra p3 p4)) E0)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE0; reflexivity]).
assert (HAG : env_agree 40 E0 E0) by (split; [intros; reflexivity | reflexivity]).
assert (Usp0 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite F2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E0 10) = cp) by (rewrite F10; apply unsigned_lit_small; lia).
clear HE0 EL.
unfold cfg_at. change (w64 (BASE + AF_check_words_pin_set)) with (Z_to_bv 64 (BASE + AF_check_words_pin_set)).
revert HS SHOK HWH. destruct (Z.ltb_spec 4 r) as [Hhi | Hlo]; intros HS SHOK HWH.
- (* r >= 5: the verdict comes from words[4] *)
destruct (HWH eq_refl) as ((b & k & Hin & Hb & He) & Hwm & Rp4).
destruct (H4 Hhi) as (_ & _ & _ & _ & Hp4b & Hp4s). clear H4.
pose proof (sready_of_blk ly S W mem md p4 w4 HAR Hp4b Hp4s) as R4.
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hk).
pose proof (req_size_pos0 k ltac:(lia)) as [Hr0 Hrk].
assert (WPB : 4064 <= wp /\ wp + 40 <= alloc_ceiling) by lia.
assert (U11 : bv_unsigned (ew E0 11) = wp) by (rewrite F11; apply unsigned_lit_small; lia).
(* the prologue, to the branch on r < 5 *)
cw_run.
psrr_branch_tok RUN BR HS SHOK CBspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite (cw_lt_atom E0 12 r 5 F12) in Hc by lia; apply Z.ltb_lt in Hc; lia end. }
(* words[4], to the strncmp call *)
cw_run.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (cw_strncmp_at ly S W regs mem md ms _ p4 w4 HJ HRO HCE HK);
[ rewrite Ra0, F34; reflexivity
| rewrite Ra1, (cw_img_atom E0 277 HEI ltac:(cbv; lia)); change 277%nat with (A_OBJ 36); rewrite V36; reflexivity
| rewrite Ra2; reflexivity
| unfold spZ at 1; rewrite Qsp, Usp0, unsigned_lit_small by lia; lia
| rewrite Qgp, F3; exact Hgp
| rewrite Qtp, F4; exact Htp
| exact Rra
| exact R4
| exact (amem8_of_blockA SEGS B LAWS ly S W mem md p4 (astr_len w4) HAR Hp4b ltac:(unfold astr_len; lia))
| exact RVERD ] |] end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & HK2 & Hfr2).
clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
cw_kept_regions HS2 Hfr2 HJ2.
clear HS SHOK HK HJ. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename HK2 into HK. rename HJ2 into HJ.
assert (E44 : ew (havoc E0 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by exact (cw_havoc_a0 E0 40 regs2).
assert (HEIx : img_env VAL A_LIM (havoc E0 40 (map (getr regs2) CLOB))) by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAGx : env_agree 40 E0 (havoc E0 40 (map (getr regs2) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]).
remember (havoc E0 40 (map (getr regs2) CLOB)) as E1 eqn:HE1. clear HE1 HAG HEI. rename HAGx into HAG. rename HEIx into HEI.
assert (SHOK : sh_ok SEGS CBx (cw_SH true) E1 (mrestrict (w_H W) mem2)).
{ apply (cw_shok true ly S W mem2 md2 E1 cp wp (proj1 HJ));
[ rewrite (cw_ew_agree 40 E0 E1 32 HAG) by lia; exact F32 | rewrite (cw_ew_agree 40 E0 E1 10 HAG) by lia; exact F10
| rewrite (cw_ew_agree 40 E0 E1 11 HAG) by lia; exact F11 | unfold A_G_REC, OFF_CALLS; lia | unfold A_G_REC, CALL_SIZE, REC_SIZE; lia |].
intros _. split; [exists b, k; split; [exact Hin | split; [exact Hb | exact He]] | lia]. }
(* strncmp(words[4], "verdict=", 8) is 0 exactly when words[4] starts with "verdict=" *)
assert (HPX : getr regs2 10 = w64 0 <-> prefixb w4 S_VERDICT = true).
{ pose proof R4 as (_ & _ & _ & [_ Hn4] & _).
destruct (cw_strncmp_prefix w4 S_VERDICT Hn4 ltac:(apply cw_notin0; vm_compute; reflexivity) ltac:(unfold S_VERDICT, str; cbn; discriminate))
as (v0 & Hv0 & Hv0i).
change (Z.of_nat (length S_VERDICT)) with 8 in Hv0. unfold NUL in Hv0.
rewrite Hcmp, Hv0, cw_prefixb_iff, <- Hv0i. split; [intros H; injection H as H; exact H | intros ->; reflexivity]. }
assert (U34 : U E1 (SOff 34 0) = p4) by (rewrite (cw_U_atom E0 E1 34 0 p4 HAG ltac:(lia) F34) by lia; lia).
assert (U44 : U E1 (SOff 44 0) = bv_unsigned (getr regs2 10)).
{ rewrite U_SOff, E44, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as RR.
unfold M64. change (bv_modulus 64) with (2 ^ 64) in RR. lia. }
(* the verdict strcmp compares against *)
assert (HY : exists y sy, U E1 (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 44 0) (SLit 1)) (SLit 3))) = y /\
sready W mem y sy /\ x3 = sy).
{ rewrite (cw_sel_U E1 34 44 p4 (bv_unsigned (getr regs2 10)) U34 U44) by (destruct R4 as (? & ? & _); lia).
assert (HPV : x3 = if prefixb w4 S_VERDICT then skipn 8 w4 else w4).
{ rewrite Hx3. unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_pin_set_c.pin_verdict.
replace (r <=? 4) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
destruct (prefixb w4 S_VERDICT) eqn:HPB.
- rewrite (proj2 HPX eq_refl). exists (p4 + 8), (skipn 8 w4).
split; [reflexivity|]. split; [|exact HPV].
apply cw_prefixb_iff in HPB. pose proof (f_equal (@length byte) HPB) as L. rewrite firstn_length in L.
change (length S_VERDICT) with 8%nat in L.
exact (sready_skipn W mem p4 w4 8 R4 ltac:(lia)).
- assert (Hv : bv_unsigned (getr regs2 10) =? 0 = false).
{ apply Z.eqb_neq. intros H0. assert (HZ : getr regs2 10 = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
apply HPX in HZ. congruence. }
rewrite Hv. exists (p4 + 0), w4. split; [reflexivity|]. split; [rewrite Z.add_0_r; exact R4 | exact HPV]. }
destruct HY as (y & sy & HYU & RY & HXY).
(* seqz/slli/add, the nargs and argument checks, to the strcmp call *)
cw_run.
lazymatch goal with HS : st_ok _ _ ?ss (restrict ?Hh ?ms) |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
let e := eval vm_compute in (sr_get (ss_regs ss) (11%bv : bv 5)) in
let Ra1 := fresh "Ra1" in
pose proof (st_ok_restrict_reg SEGS Hh E1 ss ms (11%bv : bv 5) HS) as Ra1; change (sr_get (ss_regs ss) (11%bv : bv 5)) with e in Ra1;
rewrite denot_lit_U, HYU in Ra1;
pmkst HS;
eapply SRr_bind;
[ apply (cw_strcmp_at ly S W regs mem md ms _ p3 x3 y sy HJ HRO HCE HK);
[ rewrite Ra0, (cw_ew_agree 40 E0 E1 33 HAG) by lia; rewrite F33; reflexivity
| exact Ra1
| unfold spZ at 1; rewrite Qsp, (cw_ew_agree 40 E0 E1 2 HAG) by lia; rewrite Usp0, unsigned_lit_small by lia; lia
| rewrite Qgp, (cw_ew_agree 40 E0 E1 3 HAG) by lia; rewrite F3; exact Hgp
| rewrite Qtp, (cw_ew_agree 40 E0 E1 4 HAG) by lia; rewrite F4; exact Htp
| exact Rra
| exact R3
| exact RY ] |] end.
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & HK3 & Hfr3).
jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS2.
cw_kept_regions HS2 Hfr3 HJ3.
clear HS SHOK HK HJ. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename HK3 into HK. rename HJ3 into HJ.
assert (E60 : ew (havoc E1 56 (map (getr regs3) CLOB)) 60 = getr regs3 10) by exact (cw_havoc_a0 E1 56 regs3).
assert (HEIx : img_env VAL A_LIM (havoc E1 56 (map (getr regs3) CLOB))) by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAGx : env_agree 40 E0 (havoc E1 56 (map (getr regs3) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]).
remember (havoc E1 56 (map (getr regs3) CLOB)) as E2 eqn:HE2. clear HE2 HAG HEI. rename HAGx into HAG. rename HEIx into HEI.
assert (SHOK : sh_ok SEGS CBx (cw_SH true) E2 (mrestrict (w_H W) mem3)).
{ apply (cw_shok true ly S W mem3 md3 E2 cp wp (proj1 HJ));
[ rewrite (cw_ew_agree 40 E0 E2 32 HAG) by lia; exact F32 | rewrite (cw_ew_agree 40 E0 E2 10 HAG) by lia; exact F10
| rewrite (cw_ew_agree 40 E0 E2 11 HAG) by lia; exact F11 | unfold A_G_REC, OFF_CALLS; lia | unfold A_G_REC, CALL_SIZE, REC_SIZE; lia |].
intros _. split; [exists b, k; split; [exact Hin | split; [exact Hb | exact He]] | lia]. }
(* bnez a0: strcmp returned 0, so the abort edge is not taken *)
psrr_branch_tok RUN BR HS SHOK CBspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite (cw_ne0_false E2 60 (getr regs3 10) E60 (proj2 Hcmp3 HXY)) in Hc; discriminate Hc end. }
(* the epilogue and the return *)
cw_run.
cw_leaf.
- (* r < 5: the verdict is "-" *)
clear HWH H4.
cw_run.
psrr_branch_tok RUN BR HS SHOK CBspan.
2:{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite (cw_lt_atom E0 12 r 5 F12) in Hc by lia; apply Z.ltb_ge in Hc; lia end. }
assert (HXY : x3 = S_DASH).
{ rewrite Hx3. unfold OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_pin_set_c.pin_verdict.
replace (r <=? 4) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
cw_run.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
pmkst HS;
eapply SRr_bind;
[ apply (cw_strcmp_at ly S W regs mem md ms _ p3 x3 0x21ac0 S_DASH HJ HRO HCE HK);
[ rewrite Ra0, F33; reflexivity
| rewrite Ra1, (cw_img_atom E0 270 HEI ltac:(cbv; lia)); change 270%nat with (A_OBJ 29); rewrite V29; reflexivity
| unfold spZ at 1; rewrite Qsp, Usp0, unsigned_lit_small by lia; lia
| rewrite Qgp, F3; exact Hgp
| rewrite Qtp, F4; exact Htp
| exact Rra
| exact R3
| exact RDASH ] |] end.
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & HK3 & Hfr3).
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3]%nat HS2.
cw_kept_regions HS2 Hfr3 HJ3.
clear HS SHOK HK HJ. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename HK3 into HK. rename HJ3 into HJ.
assert (E44 : ew (havoc E0 40 (map (getr regs3) CLOB)) 44 = getr regs3 10) by exact (cw_havoc_a0 E0 40 regs3).
assert (HEIx : img_env VAL A_LIM (havoc E0 40 (map (getr regs3) CLOB))) by (apply img_env_havoc; [exact HEI | apply Nat.leb_le; vm_compute; reflexivity]).
assert (HAGx : env_agree 40 E0 (havoc E0 40 (map (getr regs3) CLOB))) by (apply env_agree_havoc_ge; [lia | exact HAG]).
remember (havoc E0 40 (map (getr regs3) CLOB)) as E1 eqn:HE1. clear HE1 HAG HEI. rename HAGx into HAG. rename HEIx into HEI.
assert (SHOK : sh_ok SEGS CBx (cw_SH false) E1 (mrestrict (w_H W) mem3)).
{ apply (cw_shok false ly S W mem3 md3 E1 cp wp (proj1 HJ));
[ rewrite (cw_ew_agree 40 E0 E1 32 HAG) by lia; exact F32 | rewrite (cw_ew_agree 40 E0 E1 10 HAG) by lia; exact F10
| rewrite (cw_ew_agree 40 E0 E1 11 HAG) by lia; exact F11 | unfold A_G_REC, OFF_CALLS; lia | unfold A_G_REC, CALL_SIZE, REC_SIZE; lia |].
intros X. discriminate X. }
psrr_branch_tok RUN BR HS SHOK CBspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite (cw_ne0_false E1 44 (getr regs3 10) E44 (proj2 Hcmp3 HXY)) in Hc; discriminate Hc end. }
cw_run.
cw_leaf.
Qed.
End e.
End f.
End d.
