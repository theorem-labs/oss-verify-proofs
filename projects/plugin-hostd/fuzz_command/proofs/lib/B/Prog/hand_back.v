(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of hand_back (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_hand_back = 0x8a978, 38 instructions, 152 bytes): it proves a Theorem Labs lane's
   `thand_back_spec` (lib/B/Prog/hand_back_c.v, a working branch f490061c104) in the form of cgif_file_fuzzer's
   per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract listing between the
   calls, the free through the 04 allocator rules, the strlen wrapper through PaArt's aj_art_at, xmalloc through
   PaCall's cl_callS, __asan_memcpy through PaCall's aj_intrin_atS, the return through paj_ret_at, and apost_base at
   the end. The frame chains at the calls (a Theorem Labs lane's PASS4-REFIT.md section B): s0 is the caller's buffer, an object
   of a side-stack frame below alloc_ceiling (class D), so xmalloc's achain is achain_low and the free wrapper's
   chain_pre is achain_chain_pre of it; no presence of the stack up to ly_top is used.

   It is the B re-walk of the A walk lib/A/Prog/hand_back.v (a working branch 9d24669319c), which calls
   xstrdup twice (the second a tail call); B inlines both xstrdup calls (strlen, xmalloc, __asan_memcpy each), so the
   two copies are walked here as the A side's xstrdup walk walks its one copy (a working branch
   4fcb3ab49d9, xstrdup.v.green). The B code template was also read from the Generation-N walk
   lib/B/Prog/hand_back.v (template only, not ported: a working branch 543f2c3645b).

   B's code (capstone on fuzz_command.asan-ubsan, symbol hand_back, LOCAL FUNC 0x8a978, 152 bytes):
     0x8a978 addi sp,sp,-48; sd ra,40(sp); sd s0,32(sp); sd s1,24(sp); sd s2,16(sp); sd s3,8(sp)
     0x8a990 auipc s3 (A_HI 121 = 0x5e3990); ld a1,-0x340(s3) (A_OBJ 55 = 0x5e3650 = g_rec.answer); mv s0,a0; mv a0,a1
     0x8a9a0 jal __interceptor_trampoline_free (0x589cc)
     0x8a9a4 mv a0,s0; jal __interceptor_trampoline_strlen (0x4517c) at 0x8a9a8
     0x8a9ac addi s1,a0,1; mv a0,s1; jal xmalloc (0x899b4) at 0x8a9b4
     0x8a9b8 mv s2,a0; mv a1,s0; mv a2,s1; jal __asan_memcpy (0x5767c) at 0x8a9c4
     0x8a9c8 sd s2,-0x340(s3) (g_rec.answer := the first copy, a plain word through the auipc base A_HI 121)
     0x8a9cc mv a0,s0; jal strlen at 0x8a9d0; addi s1,a0,1; mv a0,s1; jal xmalloc at 0x8a9dc
     0x8a9e0 mv s2,a0; mv a1,s0; mv a2,s1; jal __asan_memcpy at 0x8a9ec
     0x8a9f0 mv a0,s2; ld ra/s0/s1/s2/s3; addi sp,sp,48; ret
   The only auipc (0x8a990) is the base of the load at 0x8a994 (listing PLdHi, A_OBJ 55) and of the store at 0x8a9c8
   (a plain word through A_HI 121): the store's region is seated at the auipc atom, whose value is cmd_val_his.
   Report / trap edges: the function has no branch, no `jal __asan_report_*` and no UBSan trap (no unimp / ebreak;
   measured with capstone), so it has no edge to refute here; the checks of the copies are the strlen wrapper's and
   __asan_memcpy's, whose contracts this walk takes.

   Section hypotheses beyond the statement's: HB (the allocator record) and MTL (the meter's laws), as the A walk
   names them; and the per-binary facts a Theorem Labs lane proves only at the pinned image (PI := PB_cmd), each under a Theorem Labs lane's lemma
   name with its statement at this walk's abstract PAImg: `cmd_val_his_PB : cmd_val_his` (the auipc value A_HI 121 of
   the store at 0x8a9c8), `cmd_sig_prog_PB : cmd_sig_prog` (xmalloc's call target), `cmd_img_facts_tfib`
   (lib/B/Prog/CmdRecImg.v), `cmd_palib` (lib/B/Prog/CmdRecRest.v, the free trampoline's pc), and
   `PRW : prog_rw SEGS B` (the hypothesis of lib/B/Prog/CmdRecCells.v PROG_WRITABLE, for the store's region). Every
   other per-binary fact is a Theorem Labs lane's lemma over them, by exact: CmdRecRo.v RELRO_IMG, ROB; CmdRecRest.v
   cmd_ro_prog_apart, cmd_prog_img; CmdRecImg.v cmd_prog_unowned, cmd_rom_view_on; CmdRecCells.v cmd_cf_env,
   PROG_WRITABLE. The reader and list lemmas shared with the other recorder walks are the kit's (lib/B/Prog/RecBLemmas.v,
   a working branch 707acd856cb): aval_mem_view, val_mem_view, lay_blocks_in, recb_pair_dec, recb_run_keeps_m. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecImg CmdRecCells CmdRecRo CmdRecRest RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the atoms, the regions and the footprint (lib/B/Prog/CmdList.v, CmdAddr.v) --------------------------- *)
(* g_rec.answer (cmd_objs index 55 = 0x5e3650 = g_rec + 912) and the auipc value of the store (cmd_his index 121 =
   0x5e3990); the answer's value at the entry is the extra atom 32 *)
Definition HBB_ANS_OBJ : nat := 55.
Definition HBB_ANS_HI : nat := 121.
Definition L_OLD : nat := 32.
Definition hbb_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* the entry: the 48-byte frame below sp, and g_rec.answer read-only for the load at 0x8a994 *)
Definition hbb_ss0 : sstate :=
  mkSS AF_hand_back sr_atoms [stack_region 48; obj8_region HBB_ANS_OBJ (SOff L_OLD 0)] None hbb_facts0.
(* the region of the store at 0x8a9c8 (seated after the first copy), based at the auipc atom A_HI 121 *)
Definition hbb_store_region : YP09.region :=
  YP09.mkRegion (Some (A_HI HBB_ANS_HI)) (-0x340) (-0x338) (-0x340) (-0x338) [].
(* the footprint the statement gives (hand_back_c.v, apost_base's region list) *)
Definition hbb_FP (old : Z) (O : list (Z * Z)) : list (Z * Z) :=
  (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) O).
(* the bytes and the shadow bytes of a side-stack frame *)
Definition hbb_frz (ly : alayout) (cid pos a : Z) : Prop :=
  in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).

(* ---- list and reader lemmas (the A walk's, lib/A/Prog/hand_back.v:55-72, 229-373) --------------------------- *)
Lemma hbb_in_filter : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
In pn l -> f pn = true -> In pn (filter (fun q : Z * Z => f q) l).
Proof.
intros f pn l Hin Hf. induction l as [|q l IH]; [destruct Hin|].
cbn [In] in Hin. cbn. destruct (decide (f q)) as [Hq|Hq].
- cbn [In]. destruct Hin as [Heq|Hin]; [left; exact Heq | right; exact (IH Hin)].
- destruct Hin as [Heq|Hin]; [exfalso; apply Hq; subst q; rewrite Hf; exact I | exact (IH Hin)].
Qed.
Lemma hbb_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
In pn (filter (fun q : Z * Z => f q) l) -> In pn l /\ f pn = true.
Proof.
intros f pn l. induction l as [|q l IH]; [intros []|].
cbn. destruct (decide (f q)) as [Hq|Hq].
- intros [Heq|Hin].
  + split; [left; exact Heq|]. subst q. destruct (f pn) eqn:Ef; [reflexivity | destruct Hq].
  + destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
- intros Hin. destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.
Lemma hbb_aval_kept_rng : forall (rd rd' : reader) a n v (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= a -> a + Z.of_nat n <= hi -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v lo hi HK Hlo Hhi H k Hk. rewrite (HK (a + Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.
Lemma hbb_abytes_kept_rng : forall (rd rd' : reader) p l (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= p -> p + Z.of_nat (length l) <= hi ->
abytes_atR rd p l -> abytes_atR rd' p l.
Proof. intros rd rd' p l lo hi HK Hlo Hhi H i Hi. rewrite (HK (p + Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma hbb_astr_kept_rng : forall (rd rd' : reader) p s (lo hi : Z),
(forall b, lo <= b < hi -> rd' b = rd b) -> lo <= p -> p + Z.of_nat (length s) + 1 <= hi ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s lo hi HK Hlo Hhi [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
rewrite length_app in Hi. cbn [length] in Hi.
rewrite (HK (p + Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
(* a string moved: the bytes at p are the bytes at s, through the terminator *)
Lemma hbb_astr_move : forall (rd rd' : reader) s p x,
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (s + i)) -> astr_atR rd s x -> astr_atR rd' p x.
Proof.
intros rd rd' s p x Hm [Hb Hz]. split; [|exact Hz]. intros i Hi. rewrite Hm; [apply Hb; exact Hi|].
rewrite length_app in Hi; cbn in Hi; lia.
Qed.
Lemma hbb_astr_some : forall (rd : reader) p x a, astr_atR rd p x -> p <= a < p + (Z.of_nat (length x) + 1) -> rd a <> None.
Proof.
intros rd p x a [Hb _] Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite Hb; [discriminate|].
rewrite length_app; cbn; lia.
Qed.
Lemma hbb_tail_below8 : forall e c, 0 <= e < c -> c mod 8 = 0 -> e - e mod 8 + 8 <= c.
Proof.
intros e c He Hc. assert (Hlt : e / 8 < c / 8) by (apply Z.div_lt_upper_bound; [lia|];
  pose proof (Z_div_mod_eq_full c 8); lia).
pose proof (Z_div_mod_eq_full e 8). pose proof (Z_div_mod_eq_full c 8). lia.
Qed.
Lemma hbb_shadow_in_frame : forall fa fs p n x,
fa mod 8 = 0 -> fs = 8 * (fs / 8) -> fa <= p -> p + n <= fa + fs -> p <= x < p + n ->
shadow_addr fa <= SHADOW_OFF + x / 8 < shadow_addr fa + fs / 8.
Proof.
intros fa fs p n x Hal Hfs Hp Hpn Hx. pose proof (Z_div_mod_eq_full fa 8) as Hfa. rewrite Hal, Z.add_0_r in Hfa.
assert (Hle : fa / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (Hlt : x / 8 < fa / 8 + fs / 8) by (apply Z.div_lt_upper_bound; lia).
unfold shadow_addr. lia.
Qed.
Lemma hbb_rest_lay : forall Q pn,
In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hin. unfold lay_blocks.
apply in_app_or in Hin as [Hc | Hin]; [apply in_or_app; left; exact Hc|].
apply in_app_or in Hin as [Hs | Hr]; apply in_or_app; right;
[apply in_or_app; left; exact Hs | apply in_or_app; right; apply in_or_app; right; exact Hr].
Qed.
Lemma hbb_nodup_del : forall (L1 L2 L3 : list Z) (a : Z),
NoDup (L1 ++ L2 ++ a :: L3) -> NoDup (L1 ++ L2 ++ L3).
Proof.
intros L1 L2 L3 a H. apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
rewrite app_assoc in H. rewrite app_assoc. exact (NoDup_remove_1 _ _ _ H).
Qed.
Lemma hbb_nodup_ins : forall (L1 L2 L3 : list Z) (b : Z),
NoDup (L1 ++ L2 ++ L3) -> ~ In b (L1 ++ L2 ++ L3) -> NoDup (L1 ++ L2 ++ b :: L3).
Proof.
intros L1 L2 L3 b Hnd Hni. apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd.
rewrite app_assoc. apply (Permutation_NoDup (l := b :: ((L1 ++ L2) ++ L3))).
- apply Permutation_middle.
- constructor; [rewrite <- app_assoc; exact Hni | rewrite <- app_assoc; exact Hnd].
Qed.
(* a fresh block, apart from every block of a list, is not in it *)
Lemma hbb_apart_notin : forall p n bl, 1 <= n -> Forall (fun qk => iv_apart p n (fst qk) (snd qk)) bl -> ~ In (p, n) bl.
Proof.
intros p n bl Hn HF Hin. pose proof (proj1 (Forall_forall _ _) HF (p, n) Hin) as Hap. cbn [fst snd] in Hap.
unfold iv_apart in Hap. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* cgif's region_kept over aview for a region whose window bytes stay present (lv2_refusals_forget's B walk,
   lrfb_region_kept_hi2) *)
Lemma hbb_region_kept_hi2 : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma hbb_aval_det : forall H mem a v1 v2, 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 ->
aval_mem (aview SEGS H mem) a 8 v1 -> aval_mem (aview SEGS H mem) a 8 v2 -> v1 = v2.
Proof.
intros H mem a v1 v2 Hv1 Hv2 H1 H2.
pose proof (rdword_of_val_mem SEGS H mem a v1 (val_mem_view SEGS H mem a 8 v1 H1) Hv1) as E1.
pose proof (rdword_of_val_mem SEGS H mem a v2 (val_mem_view SEGS H mem a 8 v2 H2) Hv2) as E2.
rewrite E1 in E2. injection E2 as E2. exact E2.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (each at every FP state), runtime entries and object bridge (hand_back_c.v:64-69) *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1: the per-binary allocator record (lib/B/YF0m.v) and the
   meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the per-binary facts a Theorem Labs lane proves at the pinned image only, under a Theorem Labs lane's lemma names (lib/B/Prog/CmdRecRest.v,
   CmdRecImg.v), at this walk's abstract PAImg *)
Hypothesis cmd_val_his_PB : cmd_val_his.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> @PALib rc cmd_listing PI B0.
(* the program's statics are writable at every state (the core's prog_rw, the hypothesis of a Theorem Labs lane's
   CmdRecCells.v PROG_WRITABLE) *)
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let TL : @PALib rc cmd_listing PI B := cmd_palib B HB.
Let ENV : api_env SEGS B := cmd_cf_env SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a :=
  CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---- the image's words the walk names -------------------------------------------------------------------- *)
Lemma hbb_val_ans : VAL (A_OBJ HBB_ANS_OBJ) = A_G_REC + OFF_ANSWER.
Proof. rewrite (VOBJS HBB_ANS_OBJ ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma hbb_val_hi : VAL (A_HI HBB_ANS_HI) = A_G_REC + OFF_ANSWER + 0x340.
Proof. rewrite (cmd_val_his_PB HBB_ANS_HI ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma hbb_sig_xmalloc : SIG CS_xmalloc = BASE + AF_xmalloc.
Proof.
rewrite (cmd_sig_prog_PB CS_xmalloc ltac:(unfold cmd_prog_syms; cbn [In]; repeat (try (now left); right))).
reflexivity.
Qed.
Lemma hbb_ans_PG : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd]. unfold A_G_REC, OFF_ANSWER in *. lia. Qed.
Lemma hbb_ans_static : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, OFF_ANSWER in Ha. lia. Qed.
Lemma hbb_ans_img : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a (hbb_ans_static a Ha))). Qed.
(* a write of the walk to g_rec.answer: the footprint names it, and it is a program static of the image *)
Lemma hbb_awr_ans : forall STK sp0 old O bl0 blc fr0 ly own a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 ->
awr_byte SEGS B STK sp0 (hbb_FP old O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 old O bl0 blc fr0 ly own a Ha. right; right; right; right. left.
split; [apply (proj2 (inFP_cons _ _ _ a)); left; exact Ha|].
split; [rewrite (ts_prog B HB); exact (hbb_ans_static a Ha) | exact (cmd_prog_img a (hbb_ans_static a Ha))].
Qed.

(* ---- the footprint ------------------------------------------------------------------------------------------ *)
Lemma hbb_FP_inv : forall old O a, inFP (hbb_FP old O) a ->
(A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) \/
exists p m, In (p, m) O /\ p = old /\ p <= a < p + req_size m.
Proof.
intros old O a Hin. unfold hbb_FP in Hin. apply (proj1 (inFP_cons _ _ _ a)) in Hin as [Hin | Hin]; [left; exact Hin|].
right. destruct (inFP_ablocks_fp_inv _ a Hin) as (p & m & Hpm & Hr).
destruct (hbb_filter_in _ _ _ Hpm) as [HinO Hf]. cbn [fst] in Hf. apply Z.eqb_eq in Hf.
exists p, m. auto.
Qed.
Lemma hbb_FP_sink : forall ly S (W : world SEGS) mem md old O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> ~ YI16.sink_open_fp (hbb_FP old O).
Proof.
intros ly S W mem md old O HAR HO. unfold hbb_FP. apply sink_closed_cons; [cbn [fst]; unfold A_G_REC, OFF_ANSWER; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p m] Hpm. destruct (hbb_filter_in _ _ _ Hpm) as [HinO _].
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR (HO _ HinO)) as (_ & H4 & _). cbn [fst]. lia.
Qed.
(* a read-only byte is no footprint byte: the answer word is a program static, the blocks lie off the image *)
Lemma hbb_FP_ro : forall ly S (W : world SEGS) mem md old O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> in_roP SEGS RLO RHI a -> ~ inFP (hbb_FP old O) a.
Proof.
intros ly S W mem md old O a HAR HO Hro Hin. destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct (hbb_FP_inv old O a Hin) as [Ha | (p & m & Hpm & _ & Hr)]; [exact (HnPG (hbb_ans_static a Ha))|].
pose proof (blk_off_imgP B ly S W mem md p m HAR (HO _ Hpm)) as Hoff. unfold off_img in Hoff.
pose proof (pa_img_range a Himg). lia.
Qed.
Lemma hbb_aro : forall ly S (W : world SEGS) mem md old O STK sp0 own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (hbb_FP old O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros ly S W mem md old O STK sp0 own ly' S' W' mem' md' k HAR HO HJ HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B STK sp0 (hbb_FP old O) ly S W mem md own ly' S' W' mem' md' k HJ);
[|exact HR]. intros a Hro. exact (hbb_FP_ro ly S W mem md old O a HAR HO Hro).
Qed.

(* ---- the caller's buffer: a side-stack frame object ------------------------------------------------------- *)
Lemma hbb_frz_bounds : forall ly S (W : world SEGS) mem md cid pos a, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
hbb_frz ly cid pos a -> 0 <= a < alloc_ceiling /\ (a < 0x10000 \/ 0x606000 <= a).
Proof.
intros ly S W mem md cid pos a HAR Hfr Ha.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hb1 & Hb2 & Hb3).
pose proof (fs_frame_bytes_nonneg cid) as Hfsnn. pose proof asan_consts as (C1 & _).
assert (Hsh8 : 8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
assert (Hsh0 : 0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
assert (Hdv1 : 0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia).
assert (Hdv2 : 8 * (frame_addr ly cid pos / 8) <= frame_addr ly cid pos) by (apply Z.mul_div_le; lia).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfr) as Hfimg. unfold off_img in Hfimg.
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; lia.
Qed.
Lemma hbb_frz_blk : forall ly S (W : world SEGS) mem md cid pos b m a, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
In (b, m) (ablocks B ly S) -> hbb_frz ly cid pos a -> ~ (b <= a < b + req_size m).
Proof.
intros ly S W mem md cid pos b m a HAR Hfr Hin Ha Hab.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbk).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf1 & Hf2 & _).
pose proof asan_consts as (C1 & _).
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- pose proof (sep_block_frame SEGS B LAWS ly S W mem md b m cid pos HAR Hin Hfr) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- exact (fshadow_not_app (frame_addr ly cid pos) (fs_frame_bytes cid / 8) b (req_size m) a
    ltac:(lia) ltac:(pose proof (fs_frame_bytes_nonneg cid); pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)); lia)
    Hbapp ltac:(unfold shadow_addr, SHADOW_OFF in Ha; lia) Hab).
Qed.
Lemma hbb_frz_FP : forall ly S (W : world SEGS) mem md cid pos old O a, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> hbb_frz ly cid pos a -> ~ inFP (hbb_FP old O) a.
Proof.
intros ly S W mem md cid pos old O a HAR Hfr HO Ha Hin.
destruct (hbb_FP_inv old O a Hin) as [Hans | (p & m & Hpm & _ & Hr)].
- pose proof (hbb_ans_img a Hans) as Hai. destruct (hbb_frz_bounds ly S W mem md cid pos a HAR Hfr Ha) as (_ & [Hl|Hl]); lia.
- exact (hbb_frz_blk ly S W mem md cid pos p m a HAR Hfr (HO _ Hpm) Ha Hr).
Qed.
(* the facts the strlen wrapper and __asan_memcpy ask of the caller's buffer, at any later state of the walk: its
   bytes and their shadow are kept by the journal's frame clause (no footprint byte lies in them), its shadow words
   are readable and the bytes after its terminator are present, both by AR's frame law at that state *)
Lemma hbb_src : forall ly S (W : world SEGS) mem md cid pos s x STK sp0 old O lyk Sk (Wk : world SEGS) memk mdk k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= s -> s + (Z.of_nat (length x) + 1) <= frame_addr ly cid pos + fs_frame_bytes cid ->
astr_atR (rdW W mem) s x -> range_addressable (rdW W mem) SHADOW_OFF s (Z.of_nat (length x) + 1) ->
ajournal SEGS B STK sp0 (hbb_FP old O) ly S W mem md [] lyk Sk Wk memk mdk k ->
(forall a, hbb_frz ly cid pos a -> rdW Wk memk a = rdW W mem a) /\
astr_atR (rdW Wk memk) s x /\ range_addressable (rdW Wk memk) SHADOW_OFF s (Z.of_nat (length x) + 1) /\
shadow_hull_vis (rdW Wk memk) s (Z.of_nat (length x) + 1) /\ amem_range s (Z.of_nat (length x) + 1) /\
atail_vis SEGS Wk memk (s + Z.of_nat (length x)).
Proof.
intros ly S W mem md cid pos s x STK sp0 old O lyk Sk Wk memk mdk k HAR HO Hfr Hcid Hfal Hfle Hfhi Hstr Hsra HJ.
pose proof HJ as (HARk & Hlyk & _ & _ & _ & Hfrsk & _ & _ & _ & _ & _ & F4 & _).
assert (Hfrk : In (cid, pos) (frames Sk)) by (rewrite Hfrsk; exact Hfr).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyk HAR Hlyk) as (_ & Efa & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf4096 & Hfceil & Hfapp).
assert (Hfs8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)).
{ rewrite (fs_frame_bytes_eq cid ltac:(lia)).
  replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (Hfsm : fs_frame_bytes cid mod 8 = 0) by (rewrite Hfs8; rewrite Z.mul_comm; apply Z.mod_mul; lia).
assert (HK : forall a, hbb_frz ly cid pos a -> rdW Wk memk a = rdW W mem a).
{ intros a Ha. apply (F4 cid pos a Hfr Ha). exact (hbb_frz_FP ly S W mem md cid pos old O a HAR Hfr HO Ha). }
split; [exact HK|].
split.
{ destruct Hstr as [Hb Hnz]. split; [|exact Hnz]. intros i Hi. rewrite (HK (s + Z.of_nat i)); [exact (Hb i Hi)|].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite length_app in Hi. cbn [length] in Hi. lia. }
split.
{ intros y Hy. destruct (Hsra y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite (HK (shadow_of_addr SHADOW_OFF y)); [exact Hsv|].
  right. unfold in_zr; cbn [fst snd]. unfold shadow_of_addr.
  exact (hbb_shadow_in_frame (frame_addr ly cid pos) (fs_frame_bytes cid) s (Z.of_nat (length x) + 1) y Hfal Hfs8 Hfle Hfhi Hy). }
split.
{ apply (shadow_hull_vis_of_frame SEGS B LAWS lyk Sk Wk memk mdk cid pos s _ HARk Hfrk); rewrite ?Efa; lia. }
split; [apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Hfapp | lia | lia | lia | lia]|].
assert (Hc8 : (frame_addr ly cid pos + fs_frame_bytes cid) mod 8 = 0) by (rewrite Zplus_mod, Hfal, Hfsm; reflexivity).
intros a Ha. pose proof (hbb_tail_below8 (s + Z.of_nat (length x)) (frame_addr ly cid pos + fs_frame_bytes cid)
  ltac:(lia) Hc8) as Htb.
destruct (al_frames _ _ LAWS lyk Sk Wk memk mdk cid pos HARk Hfrk) as (_ & _ & Hfpres & _).
rewrite Efa in Hfpres. apply (aview_some_of_apresent SEGS). apply (proj1 (Hfpres a ltac:(lia))).
Qed.
(* the read conditions of the strlen wrapper's contract (RtDefs' aread_ok) for such a buffer *)
Lemma hbb_aread : forall (W : world SEGS) regs mem s x stk,
let n := Z.of_nat (length x) + 1 in
0 <= s -> s + n <= alloc_ceiling -> n <= LMAX + 1 -> alloc_ceiling <= spZ regs - stk ->
astr_atR (rdW W mem) s x -> amem_range s n -> range_addressable (rdW W mem) SHADOW_OFF s n ->
shadow_hull_vis (rdW W mem) s n -> aread_ok SEGS stk W regs mem s n.
Proof.
intros W regs mem s x stk n Hs Hsc Hn Hsp Hstr Hamr Hra Hhull. pose proof asan_consts as (C1 & _).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [unfold LMAX in Hn; lia|].
split; [|split; [exact Hamr | split; [exact Hra | intros _; exact Hhull]]].
intros a Ha. split; [exact (hbb_astr_some _ s x a Hstr Ha)|]. unfold ascratch_stk. lia.
Qed.
(* a block made during the walk is written by __asan_memcpy: either it is no block of the entry (in_tmp_block) or
   it reuses the freed answer's block, whose bytes are in the footprint (the journal's freed-block clause) *)
Lemma hbb_awr_new : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k bl2 res m i lyq ownq,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
~ In (res, m) (ablocks B lyc Sc) -> In (res, m) bl2 -> 0 <= i < req_size m ->
awr_byte SEGS B STK sp0 FP (ablocks B ly S) bl2 (frames S) lyq ownq (res + i).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k bl2 res m i lyq ownq HJ Hnc Hin Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (in_dec recb_pair_dec (res, m) (ablocks B ly S)) as [H0 | H0].
- right. left. split; [exact (Hgone res m i H0 Hnc Hi)|]. exists res, m. split; [exact Hin | lia].
- right. right. left. exists res, m. split; [exact Hin|]. split; [exact H0 | lia].
Qed.

(* ---- the post of hand_back from the facts at its return (the A walk's, lib/A/Prog/hand_back.v:915-1260) ------- *)
Lemma hbb_post : forall ly S (W : world SEGS) mem md R O Q x old ly1 S1 ly2 S2 (W2 : world SEGS) mem2 md2
  ly3 S3 (W3 : world SEGS) mem3 md3 STK sp0 own k p1 p2 (regs3 : bvmap 5 word),
  AR SEGS B ly S W mem md ->
  arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
  (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
  aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
  Z.of_nat (length x) <= LMAX ->
  (forall pn, In pn (ablocks B ly1 S1) <-> In pn (ablocks B ly S) /\ fst pn <> old) ->
  Permutation (ablocks B ly2 S2) ((p1, Z.of_nat (length x) + 1) :: ablocks B ly1 S1) ->
  Forall (fun qk => iv_apart p1 (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B ly1 S1) ->
  AR SEGS B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly3 S3) ((p2, Z.of_nat (length x) + 1) :: ablocks B ly2 S2) ->
  Forall (fun qk => iv_apart p2 (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (ablocks B ly2 S2) ->
  ajournal SEGS B STK sp0 (hbb_FP old O) ly S W mem md own ly3 S3 W3 mem3 md3 k ->
  aval_mem (rdW W3 mem3) (A_G_REC + OFF_ANSWER) 8 p1 ->
  astr_atR (rdW W3 mem3) p1 x -> astr_atR (rdW W3 mem3) p2 x ->
  getr regs3 10 = w64 p2 -> 4096 <= p2 < 2 ^ 64 ->
  blocks_bytes S1 <= blocks_bytes S ->
  blocks_bytes S2 <= blocks_bytes S1 + LIVE_XMALLOC (Z.of_nat (length x) + 1) ->
  blocks_bytes S3 <= blocks_bytes S2 + LIVE_XMALLOC (Z.of_nat (length x) + 1) ->
  mo_le MT S S3 (XM_HAND_BACK MT x) ->
  exists p1 p2 O',
  let n := Z.of_nat (length x) + 1 in
  getr regs3 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
  (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
  (forall pn, In pn (ablocks B ly3 S3) <->
    (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
  rec_repA B ly3 S3 (rdW W3 mem3) (fst (hand_back R x)) O' /\
  (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
  astr_atR (rdW W3 mem3) p2 (snd (hand_back R x)) /\
  blocks_bytes S3 <= blocks_bytes S + LIVE_HAND_BACK x /\
  mo_le MT S S3 (XM_HAND_BACK MT x).
Proof.
intros ly S W mem md R O Q x old ly1 S1 ly2 S2 W2 mem2 md2 ly3 S3 W3 mem3 md3 STK sp0 own k p1 p2 regs3
  HAR HAREP HOQ Hans Hold Hlen HBL1 Hp1perm Hp1apart HAR2 Hp2perm Hp2apart HJ3 Vans3 Hp1str3 Hp2str Hp2r Hp2rng
  HBB1 HBB2 HBB3 MLE.
assert (HLX : LIVE_XMALLOC (Z.of_nat (length x) + 1) = Z.of_nat (length x) + 1) by (unfold LIVE_XMALLOC; lia).
pose proof asan_consts as (C1 & _).
rewrite HLX in HBB2, HBB3.
set (n := Z.of_nat (length x) + 1) in *.
assert (Hn : n = Z.of_nat (length x) + 1) by reflexivity.
assert (HObl : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (lay_blocks_in _ _ _ _ _ _ HAREP _ (proj1 (HOQ pn) Hpn))).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & F2o & F3o & _).
assert (Hp1in2 : In (p1, n) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p1 n HAR2 Hp1in2) as (_ & Hp1g & Hp1c & _ & _ & _ & _).
assert (Hp1in3 : In (p1, n) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | right; exact Hp1in2]).
assert (Hp2in3 : In (p2, n) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | left; reflexivity]).
assert (Hrqn : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p1 n HAR2 Hp1in2) as Hp1off. unfold off_img in Hp1off.
(* the two copies are fresh, and apart *)
assert (Hp12 : p1 <> p2).
{ intros Heq. pose proof (proj1 (Forall_forall _ _) Hp2apart (p1, n) Hp1in2) as Hap.
  cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
assert (HFRESH1 : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n)).
{ intros pn Hin Hne Heq. subst pn.
  assert (Hin1 : In (p1, n) (ablocks B ly1 S1)) by (apply (proj2 (HBL1 _)); split; [exact Hin | exact Hne]).
  pose proof (proj1 (Forall_forall _ _) Hp1apart _ Hin1) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
assert (HFRESH2 : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p2, n)).
{ intros pn Hin Hne Heq. subst pn.
  assert (Hin1 : In (p2, n) (ablocks B ly1 S1)) by (apply (proj2 (HBL1 _)); split; [exact Hin | exact Hne]).
  assert (Hin2 : In (p2, n) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | right; exact Hin1]).
  pose proof (proj1 (Forall_forall _ _) Hp2apart _ Hin2) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
(* what the whole call kept: the image outside the answer word, and every live block it did not free *)
assert (HFPblk : forall p m i, In (p, m) (ablocks B ly S) -> fst (p, m) <> old -> 0 <= i < req_size m ->
  ~ inFP (hbb_FP old O) (p + i)).
{ intros p m i Hin Hne Hi Hfp.
  destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & Hp4096 & Hpc & _ & _ & _ & Hm0).
  pose proof (blk_off_imgP B ly S W mem md p m HAR Hin) as Hoff. unfold off_img in Hoff.
  destruct (hbb_FP_inv old O (p + i) Hfp) as [Ha | (q & m' & Hqm & Hq & Hr)].
  - pose proof (hbb_ans_img _ Ha). lia.
  - pose proof (HObl _ Hqm) as Hinq. cbn [fst] in Hne.
    assert (Hne2 : (q, m') <> (p, m)) by (intros Heq; injection Heq as <- <-; exact (Hne Hq)).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md q m' p m HAR Hinq Hin Hne2) as Hd.
    destruct (al_blocks _ _ LAWS ly S W mem md q m' HAR Hinq) as (_ & _ & _ & _ & _ & _ & Hm'0).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (KEEPG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W3 mem3 a = rdW W mem a).
{ intros a Himg Hown Herr Hans2. apply F3o; [exact Himg | exact Hown | exact Herr|].
  apply fp_spares_closed; [exact (hbb_FP_sink ly S W mem md old O HAR HObl)|].
  intros Hfp. destruct (hbb_FP_inv old O a Hfp) as [Ha | (q & m & Hqm & _ & Hr)]; [exact (Hans2 Ha)|].
  pose proof (blk_off_imgP B ly S W mem md q m HAR (HObl _ Hqm)) as Hoff. unfold off_img in Hoff.
  pose proof (pa_img_range a Himg). lia. }
assert (KEEPB : forall p m i, In (p, m) (ablocks B ly S) -> fst (p, m) <> old -> In (p, m) (ablocks B ly3 S3) ->
  0 <= i < req_size m -> rdW W3 mem3 (p + i) = rdW W mem (p + i))
by (intros p m i Hin Hne Hin3 Hi; exact (F2o p m i Hin Hin3 Hi (HFPblk p m i Hin Hne Hi))).
exists p1, p2, (lay_blocks (RLay (l_calls Q) (l_spill Q) (Some (p1, n)) (l_reply Q))).
cbv zeta.
split; [exact Hp2r|].
split; [exact Hp2rng|].
split; [exact Hp12|].
split; [intros pn Hin Hne; split; [exact (HFRESH1 pn Hin Hne) | exact (HFRESH2 pn Hin Hne)]|].
split.
{ intros pn. split.
  - intros Hin3. apply (Permutation_in _ Hp2perm) in Hin3. destruct Hin3 as [Heq | Hin2];
    [right; right; symmetry; exact Heq|].
    apply (Permutation_in _ Hp1perm) in Hin2. destruct Hin2 as [Heq | Hin1]; [right; left; symmetry; exact Heq|].
    left. exact (proj1 (HBL1 pn) Hin1).
  - intros [[HA1 HB1] | [Heq | Heq]].
    + apply (Permutation_in _ (Permutation_sym Hp2perm)). right.
      apply (Permutation_in _ (Permutation_sym Hp1perm)). right.
      apply (proj2 (HBL1 pn)). split; [exact HA1 | exact HB1].
    + rewrite Heq. exact Hp1in3.
    + rewrite Heq. exact Hp2in3. }
(* the answer slot of the recorder's layout, and that nothing else of it starts at the old answer *)
assert (HOTH : forall pn, In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)) -> fst pn <> old).
{ pose proof HAREP as (_ & _ & _ & _ & HANS2 & _ & _ & HOWN2).
  intros pn Hin.
  assert (HinQ : In pn (lay_blocks Q)) by exact (hbb_rest_lay Q pn Hin).
  destruct (r_answer R) as [t|] eqn:ERA; destruct (l_answer Q) as [[pa pk]|] eqn:ELA;
  try (exfalso; exact HANS2).
  - destruct HANS2 as (Hva & _ & Hpain & _).
    destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
    pose proof (req_size_pos pk ltac:(lia)) as [Hrq1 Hrq2].
    assert (HpaO : pa = old)
    by (apply (hbb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact Hans]).
    rewrite <- HpaO. pose proof (proj1 HOWN2) as Hnd. unfold lay_blocks in Hnd. rewrite ELA in Hnd.
    cbn [oblk] in Hnd. rewrite !map_app in Hnd. cbn [map] in Hnd. rewrite app_assoc in Hnd.
    cbn [app fst] in Hnd. first [apply NoDup_ListNoDup in Hnd | idtac].
    pose proof (NoDup_remove_2 _ _ _ Hnd) as Hni. intros Hfp. apply Hni. rewrite <- Hfp.
    rewrite <- !map_app. apply in_map. rewrite <- app_assoc. exact Hin.
  - assert (Hold0 : old = 0)
    by (apply (hbb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hans | exact HANS2]).
    destruct pn as [pq nq]. destruct (al_blocks _ _ LAWS ly S W mem md pq nq HAR
      (lay_blocks_in _ _ _ _ _ _ HAREP _ HinQ)) as (_ & Hq4096 & _). cbn [fst]. lia. }
assert (HANSOLD : forall pa pk, l_answer Q = Some (pa, pk) -> pa = old).
{ pose proof HAREP as (_ & _ & _ & _ & HANS2 & _).
  intros pa pk ELA. destruct (r_answer R) as [t|] eqn:ERA; rewrite ELA in HANS2; [|exfalso; exact HANS2].
  destruct HANS2 as (Hva & _ & Hpain & _).
  destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
  pose proof (req_size_pos pk ltac:(lia)) as [Hrq1 Hrq2].
  apply (hbb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact Hans]. }
split.
2:{ split.
    2:{ split.
        2:{ split; [unfold LIVE_HAND_BACK, LIVE_XMALLOC; lia | exact MLE]. }
        cbn [hand_back snd]. exact Hp2str. }
    (* the recorder's own blocks after the call *)
    intros pn. unfold lay_blocks at 1. cbn [l_calls l_spill l_answer l_reply oblk].
    split.
    - intros Hin. apply in_app_or in Hin as [Hc | Hin].
      + left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; left; exact Hc|].
        apply HOTH. apply in_or_app. left. exact Hc.
      + apply in_app_or in Hin as [Hs | Hin].
        * left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hs|].
          apply HOTH. apply in_or_app. right. apply in_or_app. left. exact Hs.
        * apply in_app_or in Hin as [Ha | Hr].
          -- destruct Ha as [Heq | []]. right. symmetry. exact Heq.
          -- left. split; [apply HOQ; unfold lay_blocks; apply in_or_app; right; apply in_or_app; right;
               apply in_or_app; right; exact Hr|].
             apply HOTH. apply in_or_app. right. apply in_or_app. right. exact Hr.
    - intros [[HA1 HB1] | Heq].
      + apply HOQ in HA1. unfold lay_blocks in HA1.
        apply in_app_or in HA1 as [Hc | HA1]; [apply in_or_app; left; exact Hc|].
        apply in_app_or in HA1 as [Hs | HA1]; [apply in_or_app; right; apply in_or_app; left; exact Hs|].
        apply in_app_or in HA1 as [Ha | Hr].
        * exfalso. destruct (l_answer Q) as [[pa pk]|] eqn:ELA; cbn [oblk] in Ha; [|destruct Ha].
          destruct Ha as [Heq | []]. rewrite <- Heq in HB1. cbn [fst] in HB1.
          exact (HB1 (HANSOLD pa pk ltac:(first [exact ELA | reflexivity]))).
        * apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hr.
      + rewrite Heq. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
(* the recorder's state after the call *)
assert (KEEPREC : forall a, (A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56) ->
  ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha Hne.
  assert (HinPG : inFP cmd_PG a).
  { unfold cmd_PG. destruct Ha as [Ha | Ha];
    [apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; lia
    | apply (proj2 (inFP_cons _ _ _ a)); right; apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; lia]. }
  destruct (cmd_prog_unowned SEGS B LAWS HB IMG a HinPG) as (Himg & Hno & Herr).
  exact (KEEPG a Himg Hno Herr Hne). }
assert (HKEEPIN : forall pn, In pn (ablocks B ly S) -> fst pn <> old -> In pn (ablocks B ly3 S3)).
{ intros pn HA1 HB1. apply (Permutation_in _ (Permutation_sym Hp2perm)). right.
  apply (Permutation_in _ (Permutation_sym Hp1perm)). right.
  apply (proj2 (HBL1 pn)). split; [exact HA1 | exact HB1]. }
assert (HCALLKEEP : forall a c P, (forall b, a <= b < a + CALL_SIZE -> rdW W3 mem3 b = rdW W mem b) ->
  (forall pn, In pn P -> In pn (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q))) ->
  acall_at (ablocks B ly S) (rdW W mem) a c P -> acall_at (ablocks B ly3 S3) (rdW W3 mem3) a c P).
{ intros a c P HK HPQ (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_FN) 4 (fst c) a (a + CALL_SIZE)
    HK ltac:(unfold CALL_OFF_FN; lia) ltac:(unfold CALL_OFF_FN, CALL_SIZE; cbn; lia) H4)|].
  split; [exact (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd c)))
    a (a + CALL_SIZE) HK ltac:(unfold CALL_OFF_NARGS; lia) ltac:(unfold CALL_OFF_NARGS, CALL_SIZE; cbn; lia) H5)|].
  split; [exact H6|].
  intros k0 sv pn Hs Hp. destruct (H7 k0 sv pn Hs Hp) as (G1 & G2 & G3 & G4 & G5).
  assert (Hk6 : (k0 < 6)%nat).
  { assert (Hk' : (k0 < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate). lia. }
  assert (Hne : fst pn <> old) by (apply HOTH; apply HPQ; eapply nth_error_In; exact Hp).
  destruct pn as [pq nq]. cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS ly S W mem md pq nq HAR G3) as (_ & Hq4096 & _ & _ & _ & _ & Hnq0).
  pose proof (req_size_pos nq ltac:(lia)) as [Hrq1 Hrq2].
  assert (HKq : forall b, pq <= b < pq + req_size nq -> rdW W3 mem3 b = rdW W mem b)
  by (intros b Hb; replace b with (pq + (b - pq)) by lia; exact (KEEPB pq nq (b - pq) G3 Hne (HKEEPIN _ G3 Hne) ltac:(lia))).
  split; [exact (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (a + CALL_OFF_ARGS + 8 * Z.of_nat k0) 8 pq
    a (a + CALL_SIZE) HK ltac:(unfold CALL_OFF_ARGS; lia) ltac:(unfold CALL_OFF_ARGS, CALL_SIZE; cbn; lia) G1)|].
  split; [exact G2|]. split; [exact (HKEEPIN _ G3 Hne)|]. split; [exact G4|].
  exact (hbb_astr_kept_rng (rdW W mem) (rdW W3 mem3) pq sv pq (pq + req_size nq) HKq ltac:(lia) ltac:(lia) G5). }
assert (KREC : forall lo hi, A_G_REC <= lo -> hi <= A_G_REC + 960 ->
  (hi <= A_G_REC + OFF_ANSWER \/ A_G_REC + OFF_ANSWER + 8 <= lo) ->
  forall b, lo <= b < hi -> rdW W3 mem3 b = rdW W mem b)
by (intros lo hi H1 H2 H3 b Hb; apply KEEPREC; [left; lia | unfold OFF_ANSWER in *; lia]).
assert (KSPL : forall b, A_REC_SPILL <= b < A_REC_SPILL + 56 -> rdW W3 mem3 b = rdW W mem b)
by (intros b Hb; apply KEEPREC; [right; exact Hb | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia]).
pose proof HAREP as (Hg8 & Hsc8b & Hapb & HC & HA & HPb & HSC & HOW).
cbn [hand_back fst].
exists (RLay (l_calls Q) (l_spill Q) (Some (p1, n)) (l_reply Q)).
split; [|intros pn; split; intros Hin; exact Hin].
split; [exact Hg8|]. split; [exact Hsc8b|]. split; [exact Hapb|].
destruct HC as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6).
split.
{ cbn [l_calls l_spill r_calls r_spill set_answer].
  split; [exact Hc1|]. split; [exact Hc2|].
  split.
  { eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_NCALLS) 4
      (Z.of_nat (length (r_calls R))) (A_G_REC + OFF_NCALLS) (A_G_REC + OFF_NCALLS + 4)).
    - apply KREC; unfold OFF_NCALLS, OFF_ANSWER; [lia | lia | left; lia].
    - lia.
    - cbn. lia.
    - exact Hc3. }
  split.
  { intros i c P Hi HP'. cbn [l_calls l_spill l_answer l_reply] in HP', Hi.
    destruct (Hc4 i c P Hi HP') as [Hca Hfa]. split; [|exact Hfa].
    assert (Hi16 : (i < 16)%nat).
    { assert (Hi' : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite HP'; discriminate). lia. }
    apply (HCALLKEEP _ c P).
    - apply (KREC (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i)
        (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_SIZE));
      [unfold OFF_CALLS, CALL_SIZE; lia | unfold OFF_CALLS, CALL_SIZE; lia
      | left; unfold OFF_CALLS, CALL_SIZE, OFF_ANSWER; lia].
    - intros pn Hpn. apply in_or_app. left. apply in_concat. exists P.
      split; [eapply nth_error_In; exact HP' | exact Hpn].
    - exact Hca. }
  split; [|exact Hc6].
  apply (HCALLKEEP _ (r_spill R) (l_spill Q)).
  - intros b Hb. apply KSPL. unfold CALL_SIZE in Hb. lia.
  - intros pn Hpn. apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - exact Hc5. }
split.
{ (* the answer is the first copy *)
  cbn [r_answer set_answer l_answer].
  repeat split.
  - exact Vans3.
  - cbn [fst]. lia.
  - cbn [fst snd]. exact Hp1in3.
  - cbn [snd]. lia.
  - cbn [snd]. unfold LMAX in *. lia.
  - cbn [fst]. exact (proj1 Hp1str3).
  - cbn [fst]. exact (proj2 Hp1str3).
  - exact Hlen. }
split.
{ (* the reply is untouched *)
  cbn [r_reply set_answer l_reply].
  revert HPb. destruct (r_reply R) as [y|] eqn:ERY; destruct (l_reply Q) as [[pr nr]|] eqn:ELY;
  try (intros HPb; destruct HPb; fail).
  - intros (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    assert (Hrne : fst (pr, nr) <> old)
    by (apply HOTH; apply in_or_app; right; apply in_or_app; right;
        first [rewrite ELY | idtac]; cbn [oblk]; left; reflexivity).
    destruct (al_blocks _ _ LAWS ly S W mem md pr nr HAR R5) as (_ & Hr4096 & _ & _ & _ & _ & Hnr0).
    pose proof (req_size_pos nr ltac:(lia)) as [Hrq1 Hrq2].
    assert (HKr : forall b, pr <= b < pr + req_size nr -> rdW W3 mem3 b = rdW W mem b)
    by (intros b Hb; replace b with (pr + (b - pr)) by lia;
        exact (KEEPB pr nr (b - pr) R5 Hrne (HKEEPIN _ R5 Hrne) ltac:(lia))).
    cbn [areply_at fst snd] in *.
    split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY) 8 pr
      (A_G_REC + OFF_REPLY) (A_G_REC + OFF_REPLY + 8));
      [apply KREC; unfold OFF_REPLY, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R1]|].
    split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY_SIZE) 8
      (Z.of_nat (length y)) (A_G_REC + OFF_REPLY_SIZE) (A_G_REC + OFF_REPLY_SIZE + 8));
      [apply KREC; unfold OFF_REPLY_SIZE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R2]|].
    split; [exact R3|]. split; [exact R4|]. split; [exact (HKEEPIN _ R5 Hrne)|]. split; [exact R6|].
    split; [| exact R8].
    exact (hbb_abytes_kept_rng (rdW W mem) (rdW W3 mem3) pr y pr (pr + req_size nr) HKr ltac:(lia) ltac:(lia) R7).
  - intros (R1 & R2). cbn [areply_at] in *.
    split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY) 8 0
      (A_G_REC + OFF_REPLY) (A_G_REC + OFF_REPLY + 8));
      [apply KREC; unfold OFF_REPLY, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R1]|].
    eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REPLY_SIZE) 8 0
      (A_G_REC + OFF_REPLY_SIZE) (A_G_REC + OFF_REPLY_SIZE + 8));
    [apply KREC; unfold OFF_REPLY_SIZE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact R2]. }
split.
{ (* the scalar fields are untouched *)
  destruct HSC as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  cbn [r_refuse r_code r_nreplies r_state r_host set_answer].
  split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_REFUSE) 4 (r_refuse R)
    (A_G_REC + OFF_REFUSE) (A_G_REC + OFF_REFUSE + 4));
    [apply KREC; unfold OFF_REFUSE, OFF_ANSWER; [lia | lia | left; lia] | lia | cbn; lia | exact X1]|].
  split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_CODE) 4 (r_code R)
    (A_G_REC + OFF_CODE) (A_G_REC + OFF_CODE + 4));
    [apply KREC; unfold OFF_CODE, OFF_ANSWER; [lia | lia | left; lia] | lia | cbn; lia | exact X2]|].
  split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_NREPLIES) 4 (r_nreplies R)
    (A_G_REC + OFF_NREPLIES) (A_G_REC + OFF_NREPLIES + 4));
    [apply KREC; unfold OFF_NREPLIES, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X3]|].
  split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_STATE) 8 (r_state R)
    (A_G_REC + OFF_STATE) (A_G_REC + OFF_STATE + 8));
    [apply KREC; unfold OFF_STATE, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X4]|].
  split; [eapply (hbb_aval_kept_rng (rdW W mem) (rdW W3 mem3) (A_G_REC + OFF_HOST) 8 (r_host R)
    (A_G_REC + OFF_HOST) (A_G_REC + OFF_HOST + 8));
    [apply KREC; unfold OFF_HOST, OFF_ANSWER; [lia | lia | right; lia] | lia | cbn; lia | exact X5]|].
  split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9 | exact X10]. }
(* the recorder's own blocks: the answer slot now holds the first copy *)
assert (HNIp1 : ~ In p1 (map fst (concat (l_calls Q) ++ l_spill Q ++ oblk (l_reply Q)))).
{ intros Hin. apply in_map_iff in Hin as (pn & Hfst & Hpn).
  assert (Hne : fst pn <> old) by (apply HOTH; exact Hpn).
  assert (HinS : In pn (ablocks B ly S)) by (apply HObl; apply HOQ; apply hbb_rest_lay; exact Hpn).
  assert (Hin1 : In pn (ablocks B ly1 S1)) by (apply (proj2 (HBL1 _)); split; [exact HinS | exact Hne]).
  destruct (Z.eq_dec (snd pn) n) as [Hsz | Hsz].
  - pose proof (proj1 (Forall_forall _ _) Hp1apart _ Hin1) as Hap. cbv beta in Hap.
    rewrite Hfst, Hsz in Hap. unfold iv_apart in Hap. lia.
  - assert (Hin2 : In pn (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | right; exact Hin1]).
    destruct pn as [pq nq]. cbn [fst snd] in Hfst, Hsz. subst pq.
    assert (Hne2 : (p1, nq) <> (p1, n)) by (intros Heq; injection Heq as Heq; exact (Hsz Heq)).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p1 nq p1 n HAR2 Hin2 Hp1in2 Hne2) as Hd.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p1 nq HAR2 Hin2) as (_ & _ & _ & _ & _ & _ & Hnq0).
    pose proof (req_size_pos nq ltac:(lia)) as [Hq1 Hq2].
    pose proof (req_size_pos n ltac:(lia)) as [Hq3 Hq4].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
split.
{ unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply oblk].
  rewrite !map_app. cbn [map].
  apply hbb_nodup_ins.
  - pose proof (proj1 HOW) as Hnd. unfold lay_blocks in Hnd. rewrite !map_app in Hnd.
    destruct (l_answer Q) as [[pa pk]|] eqn:ELA; cbn [oblk map] in Hnd; [|exact Hnd].
    exact (hbb_nodup_del _ _ _ _ Hnd).
  - rewrite <- !map_app. exact HNIp1. }
intros pn Hin. unfold lay_blocks in Hin. cbn [l_calls l_spill l_answer l_reply oblk] in Hin.
apply in_app_or in Hin as [Hc | Hin].
- exact (proj2 HOW pn (hbb_rest_lay Q pn (in_or_app _ _ _ (or_introl Hc)))).
- apply in_app_or in Hin as [Hs | Hin].
  + exact (proj2 HOW pn (hbb_rest_lay Q pn (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hs)))))).
  + destruct Hin as [Heq | Hr].
    * rewrite <- Heq. cbn [fst snd]. rewrite Hrqn in Hp1off.
      unfold iv_apart, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *. split; lia.
    * exact (proj2 HOW pn (hbb_rest_lay Q pn
        (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hr)))))).
Qed.

(* no two live blocks start at the same address: the allocator's separation law (al_sep) *)
Lemma hbb_two_at : forall ly S (W : world SEGS) mem md p m1 m2 l1 l2,
AR SEGS B ly S W mem md -> ablocks B ly S = l1 ++ (p, m1) :: l2 -> In (p, m2) (l1 ++ l2) -> False.
Proof.
intros ly S W mem md p m1 m2 l1 l2 HAR Heq Hin.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
assert (Hdec : exists a1 a2 a3, ablocks B ly S = a1 ++ (p, m1) :: a2 ++ (p, m2) :: a3
 \/ ablocks B ly S = a1 ++ (p, m2) :: a2 ++ (p, m1) :: a3).
{ apply in_app_or in Hin as [Hin | Hin]; apply in_split in Hin as (b1 & b2 & Hb).
  - exists b1, b2, l2. right. rewrite Heq, Hb, <- app_assoc. reflexivity.
  - exists l1, b1, b2. left. rewrite Heq, Hb. reflexivity. }
assert (Hin1 : In (p, m1) (ablocks B ly S)) by (rewrite Heq; apply in_or_app; right; left; reflexivity).
assert (Hin2 : In (p, m2) (ablocks B ly S)).
{ rewrite Heq. apply in_app_or in Hin as [Hq | Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
destruct (al_blocks _ _ LAWS ly S W mem md p m1 HAR Hin1) as (_ & _ & _ & _ & _ & _ & Hm1).
destruct (al_blocks _ _ LAWS ly S W mem md p m2 HAR Hin2) as (_ & _ & _ & _ & _ & _ & Hm2).
pose proof (pairwise_zdisjoint_split _ (p, req_size m1) (p, req_size m2) Hp
(map_split_2 (fun b : Z * Z => (fst b, req_size (snd b))) _ _ _ Hdec)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m1 ltac:(lia)). pose proof (req_size_pos m2 ltac:(lia)). lia.
Qed.

(* ---- the walk ------------------------------------------------------------------------------------------------- *)
Theorem thand_back_holds : thand_back_spec B MT.
Proof.
unfold thand_back_spec.
intros ly S W regs mem md ch s old x R O HPRE HROD H10 Hsrng Hstr Hlen Hobj HREC Hans Hold Hev Hlive HMOK.
pose proof (@pa_B_ok _ cmd_listing PI) as HBASE.
pose proof (pa_base_lo (L := cmd_listing) (PL := PL_cmd) (PI := PI)) as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBS : HAND_BACK_STK = 16448) by (vm_compute; reflexivity).
assert (HXS : XMALLOC_STK = 16400) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hspc : alloc_ceiling + 16448 <= spZ regs) by lia.
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
assert (Hlenx : astr_len x = Z.of_nat (length x)) by reflexivity.
assert (HLX : LIVE_XMALLOC (Z.of_nat (length x) + 1) = Z.of_nat (length x) + 1) by (unfold LIVE_XMALLOC; lia).
assert (HlivN : blocks_bytes S + (Z.of_nat (length x) + 1) + (Z.of_nat (length x) + 1) <= LIVE_MAX)
  by (unfold LIVE_HAND_BACK in Hlive; rewrite HLX in Hlive; lia).
assert (HevN : st_nev S + 3 <= EV_MAX) by (unfold EV_HAND_BACK, EV_XMALLOC in Hev; lia).
assert (HMOKn : mo_ok MT S (mo_free MT + XM_XMALLOC MT (Z.of_nat (length x) + 1) + XM_XMALLOC MT (Z.of_nat (length x) + 1)))
  by exact HMOK.
assert (HXMn : 0 <= XM_XMALLOC MT (Z.of_nat (length x) + 1))
  by (unfold XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
pose proof (mo_free_nonneg MT MTL) as HFRn.
destruct HREC as (Q & HAREP & HOQ).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (lay_blocks_in _ _ _ _ _ _ HAREP _ (proj1 (HOQ pn) Hpn))).
destruct Hobj as ((cid & pos & Hfr & Hcid & Hfal & Hfle & Hfhi) & Hs8 & Hsra).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf4096 & Hfceil & Hfapp).
set (n := Z.of_nat (length x) + 1) in *.
assert (Hn : n = Z.of_nat (length x) + 1) by reflexivity.
assert (Hs4096 : 4096 <= s) by lia.
assert (Hsceil : s + n <= alloc_ceiling) by lia.
assert (HnL : n <= LMAX + 1) by lia.
pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
(* the entry state: every register its own atom, g_rec.answer's value at atom 32 *)
set (E := Eimg (Ereg regs [Z_to_bv 64 old])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E)
  by (unfold E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
  by (intros nn q Hq; unfold E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 old)
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eans : bv_unsigned (ew E (A_OBJ HBB_ANS_OBJ)) = A_G_REC + OFF_ANSWER)
  by (rewrite (HEI (A_OBJ HBB_ANS_OBJ) ltac:(unfold A_OBJ, A_TEXT, A_LIM, HBB_ANS_OBJ; lia)); exact hbb_val_ans).
assert (HS : st_ok_pi SEGS VAL E hbb_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_hand_back)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold hbb_ss0. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stack_region, obj8_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HBS. lia.
    + rewrite Eans. split; [unfold A_G_REC, OFF_ANSWER; lia|]. split; [unfold A_G_REC, OFF_ANSWER; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (A_G_REC + OFF_ANSWER) 0 8 (SOff L_OLD 0) old).
      * cbn [sv_denot]. change L_OLD with 32%nat. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * first [zside | cbn; lia].
      * first [zside | cbn; lia].
      * rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H W) mem _ _ _ Hans).
  - apply pairwise_disjoint_of_extents. unfold stack_region, obj8_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Eans.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, OFF_ANSWER. repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [hbb_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. try change (2 ^ 4) with 16. try change (2 ^ 46) with 70368744177664. try change (2 ^ 47) with 140737488355328.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
pose proof (ajournal_init SEGS B HAND_BACK_STK (hbb_FP old O) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at. change (w64 (BASE + AF_hand_back)) with (Z_to_bv 64 (BASE + AF_hand_back)).

(* ==== 0x8a978 .. 0x8a9a0: the prologue, s3 := auipc, a1 := g_rec.answer, s0 := text, a0 := a1; jal free ==== *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
clear HF HG. rename HFr into HFr1. rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1c := mdx) in *; clearbody md1c end.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -48)
  by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
assert (R3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (R4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (R10' : getr (ms_regs ms1) 10 = w64 old) by (rewrite R10; try rewrite E32; reflexivity).
assert (Hs0 : s0Z (ms_regs ms1) = s)
  by (unfold s0Z; rewrite R8, (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HchT : chain_pre ly (rdW W (ms_mem ms1)) (ms_regs ms1) []).
{ apply (achain_chain_pre ly (rdW W (ms_mem ms1)) (spZ regs + -48) s [] (ms_regs ms1)).
  - apply achain_low. lia.
  - rewrite Hsp1. lia.
  - exact Hs0.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia. }
assert (Hnev : st_nev S < EV_MAX) by lia.
assert (Hmfree : mo_ok MT S (mo_free MT)) by (apply (mo_ok_le MT MTL S (mo_free MT) _ HMOKn); lia).
pmkst HS. rewrite (pal_free B TL).
eapply SRr_bind with (R := fun (W1 : world SEGS) (c1 : config) => exists ly1 S1 regs1 mem1 md1,
  c1 = mkCfg (mkst regs1 (getr (ms_regs ms1) 1) mem1 (seg_rom SEGS)) md1 /\
  ajournal SEGS B HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly1 S1 W1 mem1 md1 1 /\
  aregs_preserved (ms_regs ms1) regs1 /\
  (forall pn, In pn (ablocks B ly1 S1) <-> In pn (ablocks B ly S) /\ fst pn <> old) /\
  blocks_bytes S1 <= blocks_bytes S /\
  mo_le MT S S1 (mo_free MT) /\
  acall_kept SEGS B ly S W (ms_mem ms1) W1 mem1 (spZ regs + -48 - ASTACK) (spZ regs + -48)
    (fun a => exists k, In (old, k) (ablocks B ly S) /\ old <= a < old + req_size k)).
{ destruct (Z.eq_dec old 0) as [HO0 | HOne].
  - eapply SRr_mono.
    { eapply (afree_null04_sub SEGS B LAWS pa_segs_low MT (AFREE_NULL4 fx) W (ms_regs ms1) (ms_mem ms1)
        HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly S md1c 0 (-48) (getr (ms_regs ms1) 1) [] HJ);
      [ rewrite R10', HO0; reflexivity | exact Hsp1 | reflexivity | lia
      | rewrite HBS, Has; lia | exact R3' | exact R4' | reflexivity | exact HraT
      | exact Hnev | exact HchT | exact Hmfree ]. }
    cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HPerm1 & Hfrs1 & HK1 & MLE1 & _).
    exists ly1, S1, regs1, mem1, md1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP1|].
    split.
    { intros pn. split.
      - intros Hin. assert (Hin0 : In pn (ablocks B ly S)) by (eapply Permutation_in; [exact HPerm1 | exact Hin]).
        split; [exact Hin0|]. intros Hf. destruct pn as [pa pk]. cbn [fst] in Hf. rewrite HO0 in Hf. subst pa.
        destruct (al_blocks _ _ LAWS ly S W mem md 0 pk HAR Hin0) as (_ & H4096 & _). lia.
      - intros [Hin _]. eapply Permutation_in; [apply Permutation_sym; exact HPerm1 | exact Hin]. }
    split; [rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPerm1); lia|].
    split; [exact MLE1|].
    destruct HK1 as (K1 & K2 & K3 & K4 & K5 & K6).
    refine (conj K1 (conj _ (conj K3 (conj _ (conj K5 K6))))).
    + intros b m i Hb Hi _. apply (K2 b m i Hb Hi). intros [].
    + intros cid0 pos0 a Hc Ha _. apply (K4 cid0 pos0 a Hc Ha). intros [].
  - pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HCALLS & HANS & HREPLY & HSCAL & HOWN).
    destruct (r_answer R) as [t|] eqn:ERA; destruct (l_answer Q) as [[pa pk]|] eqn:ELA; try (exfalso; exact HANS).
    + destruct HANS as (Hva & Hpa0 & Hpain & Hpak & Hstra & Hlent).
      destruct (al_blocks _ _ LAWS ly S W mem md pa pk HAR Hpain) as (_ & Hpa4096 & Hpaceil & _ & _ & _ & Hpkr).
      pose proof (req_size_pos pk ltac:(lia)) as [Hrqa Hrqb].
      assert (HpaO : pa = old)
      by (apply (hbb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER)); [lia | lia | exact Hva | exact Hans]).
      eapply SRr_mono.
      { eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W (ms_regs ms1) (ms_mem ms1)
          HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly S md1c 0 pa pk (-48) (getr (ms_regs ms1) 1) []
          HJ Hpain);
        [ rewrite R10', HpaO; reflexivity | exact Hsp1 | reflexivity | lia
        | rewrite HBS, Has; lia | exact R3' | exact R4' | reflexivity | exact HraT
        | exact Hnev | exact HchT | | exact Hmfree ].
        intros _ i Hi. unfold hbb_FP. apply (proj2 (inFP_cons _ _ _ (pa + i))). right.
        apply (inFP_ablocks_fp _ pa pk i); [|exact Hi].
        apply hbb_in_filter.
        - apply HOQ. unfold lay_blocks. rewrite ELA.
          apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity.
        - cbn [fst]. apply Z.eqb_eq. exact HpaO. }
      cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & (l1 & l2 & Ebl & Ebl2) & Hfrs1 & HK1 & MLE1 & _).
      exists ly1, S1, regs1, mem1, md1. split; [reflexivity|]. split; [exact HJ1|]. split; [exact HP1|].
      split.
      { intros pn. rewrite Ebl2. split.
        - intros Hin. split; [rewrite Ebl; apply in_app_or in Hin as [Hq|Hq]; apply in_or_app;
          [left; exact Hq | right; right; exact Hq]|].
          intros Hf. destruct pn as [pb pm]. cbn [fst] in Hf. rewrite <- HpaO in Hf. subst pb.
          exact (hbb_two_at ly S W mem md pa pk pm l1 l2 HAR Ebl Hin).
        - intros [Hin Hf]. rewrite Ebl in Hin. apply in_app_or in Hin as [Hq|Hq]; apply in_or_app; [left; exact Hq|].
          destruct Hq as [Hq|Hq]; [exfalso; rewrite <- Hq in Hf; cbn [fst] in Hf; exact (Hf HpaO) | right; exact Hq]. }
      split; [rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly S), Ebl2, Ebl, !bsum_app, bsum_cons;
              cbn [snd]; lia|].
      split; [exact MLE1|].
      destruct HK1 as (K1 & K2 & K3 & K4 & K5 & K6).
      refine (conj K1 (conj _ (conj K3 (conj _ (conj K5 K6))))).
      * intros b m i Hb Hi Hn'. apply (K2 b m i Hb Hi). intros Hr. apply Hn'. exists pk. rewrite <- HpaO. split; [exact Hpain | exact Hr].
      * intros cid0 pos0 a Hc Ha Hn'. apply (K4 cid0 pos0 a Hc Ha). intros Hr. apply Hn'. exists pk. rewrite <- HpaO. split; [exact Hpain | exact Hr].
    + exfalso. apply HOne.
      apply (hbb_aval_det (w_H W) mem (A_G_REC + OFF_ANSWER) old 0); [lia | lia | exact Hans | exact HANS]. }
cbv beta.
intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HP1 & HBL1 & HBB1 & MLE1 & HK1).
rewrite R1.
jafter_call_keep_pi HS 33%nat regs1 (mrestrict (w_H W1) mem1) HP1 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E (w_H W) (w_H W1) (ms_mem ms1) mem1 2 (spZ regs)); [exact Usp | |].
  - intros a Ha. apply (proj1 HK1); lia.
  - intros a Ha. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS R1 R2 R3 R4 R8 R10 R3' R4' R10' HchT. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs1) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 33)%nat -> ew E1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E1)
  by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
assert (E1s : ew E1 10 = w64 s) by (rewrite OLD1 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E1gp : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E1tp : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).

(* ==== 0x8a9a4 .. 0x8a9a8: a0 := text; jal strlen ==== *)
paj_run_shc RUNP RUNC HS HJ1.
{ awr_ok_tac. exact Usp1. }
clear HF HG. rename HFr into HFr2. rename ms into ms2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2c := mdx) in *; clearbody md2c end.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
assert (Hsp2 : spZ (ms_regs ms2) = spZ regs + -48) by (unfold spZ at 1; rewrite Q2, Usp1; apply unsigned_lit_small; lia).
destruct (hbb_src ly S W mem md cid pos s x HAND_BACK_STK (spZ regs) old O ly1 S1 W1 (ms_mem ms2) md2c 1
  HAR HO Hfr Hcid Hfal Hfle Hfhi Hstr Hsra HJ1) as (_ & Hstr2 & Hra2 & Hhull2 & Hamr2 & Htail2).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms2)))
  by exact (hbb_aro ly S W mem md old O _ _ _ _ _ _ _ _ _ HAR HO HJ1 HROD).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ENV ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen) W1
    (ms_regs ms2) (ms_mem ms2) HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly1 S1 md2c 1 (-48)
    (getr (ms_regs ms2) 1) (fun regs' _ => getr regs' 10 = w64 (astr_len x)) HJ1).
  - exact Hsp2.
  - reflexivity.
  - lia.
  - lia.
  - rewrite Hes, HBS. lia.
  - reflexivity.
  - intros a [].
  - apply (ASTRLEN fx ly1 S1 W1 (ms_regs ms2) (ms_mem ms2) md2c s x).
    + apply (ecall_pre_stk_at SEGS B ESTACK HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly1 S1 W1
        (ms_mem ms2) md2c 1 (ms_regs ms2) (-48) HJ1 Hsp2 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HBS; lia)).
      * rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      * rewrite Q3. exact E1gp.
      * rewrite Q4. exact E1tp.
    + rewrite Q10. exact E1s.
    + lia.
    + apply astr_atR_view. exact Hstr2.
    + rewrite Hlenx. apply (hbb_aread W1 (ms_regs ms2) (ms_mem ms2) s x ESTACK);
      [lia | lia | lia | rewrite Hsp2, Hes; lia | exact Hstr2 | exact Hamr2 | exact Hra2 | exact Hhull2].
    + rewrite Hlenx. exact Htail2.
    + exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W1 (ms_mem ms2) HROD2). }
cbv beta. intros W1x c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
rewrite Q1.
jafter_call_keep_pi HS 49%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E1 (w_H W1) (w_H W1) (ms_mem ms2) mem2 2 (spZ regs)); [exact Usp1 | |].
  - intros a Ha. apply HK2; [lia | lia | intros []].
  - intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS Q1 Q2 Q3 Q4 Q10. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E1 49 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall nn, (nn < 49)%nat -> ew E2 nn = ew E1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
assert (E53 : ew E2 53 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp1).

(* ==== 0x8a9ac .. 0x8a9b4: s1 := |text| + 1, a0 := s1; jal xmalloc ==== *)
paj_run_shc RUNP RUNC HS HJ2.
{ awr_ok_tac. exact Usp2. }
clear HF HG. rename HFr into HFr3. rename ms into ms3. rename HJ2 into HJx1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3c := mdx) in *; clearbody md3c end.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
assert (Hsp3 : spZ (ms_regs ms3) = spZ regs + -48) by (unfold spZ at 1; rewrite T2, Usp2; apply unsigned_lit_small; lia).
assert (Hs03 : s0Z (ms_regs ms3) = s) by (unfold s0Z; rewrite T8, OLD2, E1s by lia; apply unsigned_lit_small; lia).
assert (T10' : getr (ms_regs ms3) 10 = w64 n).
{ rewrite T10, E53, HQ2, Hlenx. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hnev3 : st_nev S1 + EV_XMALLOC <= EV_MAX).
{ pose proof HJx1 as (_ & _ & _ & _ & _ & _ & Hn3 & _). unfold EV_XMALLOC. lia. }
assert (Hlive3 : blocks_bytes S1 + LIVE_XMALLOC n <= LIVE_MAX) by (rewrite HLX; lia).
assert (Hmok3 : mo_ok MT S1 (XM_XMALLOC MT n)).
{ apply (mok_station MT S S1 _ (mo_free MT) (XM_XMALLOC MT n) MTL HMOKn MLE1); lia. }
pmkst HS. rewrite hbb_sig_xmalloc.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W1 (ms_regs ms3) (ms_mem ms3) _ HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md []
    ly1 S1 md3c 1 XMALLOC_STK [] EV_XMALLOC (-48) (getr (ms_regs ms3) 1) [] _ HJx1).
  - exact Hsp3.
  - reflexivity.
  - lia.
  - rewrite HXS. lia.
  - rewrite HXS, HBS. lia.
  - rewrite T3, OLD2 by lia. exact E1gp.
  - rewrite T4, OLD2 by lia. exact E1tp.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite T1, unsigned_lit_small by lia. lia.
  - rewrite Hs03. apply achain_low. lia.
  - intros HPREc. eapply SRr_mono.
    { apply (TXMALLOC fx ly1 S1 W1 (ms_regs ms3) (ms_mem ms3) md3c [] n HPREc T10').
      - unfold MALLOC_MAX, LMAX in *. lia.
      - exact Hnev3.
      - exact Hlive3.
      - exact Hmok3. }
    intros W2 c3 _ Hc3. exact Hc3.
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta.
intros W2 c3 Hwle3 (ly2 & S2 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (p1 & Hp1r & Hp1rng & Hp1perm & Hp1apart & Hp1blk & HBB3 & MLE3)).
rewrite HLX in Hp1perm, Hp1apart, Hp1blk.
rewrite T1.
jafter_call_keep_pi HS 65%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E2 (w_H W1) (w_H W2) (ms_mem ms3) mem3 2 (spZ regs)); [exact Usp2 | |].
  - intros a Ha. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HXS; lia | apply inFP_nil].
  - intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS T1 T2 T3 T4 T8 T10 T10'. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E2 65 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall nn, (nn < 65)%nat -> ew E3 nn = ew E2 nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E3)
  by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (E69 : ew E3 69 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).

(* ==== 0x8a9b8 .. 0x8a9c4: s2 := the first copy, a1 := text, a2 := s1; jal __asan_memcpy ==== *)
paj_run_shc RUNP RUNC HS HJ3.
{ awr_ok_tac. exact Usp3. }
clear HF HG. rename HFr into HFr4. rename ms into ms4.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4c := mdx) in *; clearbody md4c end.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
assert (Hsp4 : spZ (ms_regs ms4) = spZ regs + -48) by (unfold spZ at 1; rewrite U2, Usp3; apply unsigned_lit_small; lia).
assert (U10' : getr (ms_regs ms4) 10 = w64 p1) by (rewrite U10, E69; exact Hp1r).
assert (U11' : getr (ms_regs ms4) 11 = w64 s) by (rewrite U11, OLD3, OLD2 by lia; exact E1s).
assert (U12' : getr (ms_regs ms4) 12 = w64 n).
{ rewrite U12, OLD3, E53, HQ2, Hlenx by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pose proof (proj1 HJ3) as HAR4.
pose proof HJ3 as (_ & Hly4 & _ & _ & _ & Hfrs4 & _).
assert (Hp1in : In (p1, n) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp1perm | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p1 n HAR4 Hp1in) as (_ & Hp14096 & Hp1ceil & _ & _ & _ & _).
pose proof (blk_off_imgP B ly2 S2 W2 (ms_mem ms4) md4c p1 n HAR4 Hp1in) as Hp1off. unfold off_img in Hp1off.
assert (Hp1n1 : ~ In (p1, n) (ablocks B ly1 S1)) by (apply hbb_apart_notin; [lia | exact Hp1apart]).
destruct (hbb_src ly S W mem md cid pos s x HAND_BACK_STK (spZ regs) old O ly2 S2 W2 (ms_mem ms4) md4c (1 + EV_XMALLOC)
  HAR HO Hfr Hcid Hfal Hfle Hfhi Hstr Hsra HJ3) as (_ & Hstr4 & Hra4' & Hhull4 & Hamr4 & _).
assert (Hfr2 : In (cid, pos) (frames S2)) by (rewrite Hfrs4; exact Hfr).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly4) as (_ & Efa2 & _).
assert (Hdisj4 : p1 + n <= s \/ s + n <= p1).
{ pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms4) md4c p1 n cid pos HAR4 Hp1in Hfr2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa2 in Hd. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W2 (ms_regs ms4) (ms_mem ms4)
    HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly2 S2 md4c (1 + EV_XMALLOC) p1 s n (-48)
    (getr (ms_regs ms4) 1) HJ3).
  - exact U10'.
  - exact U11'.
  - exact U12'.
  - unfold LMAX in *. lia.
  - lia.
  - lia.
  - exact Hsp4.
  - reflexivity.
  - lia.
  - rewrite Hes, HBS. lia.
  - rewrite U3, OLD3, OLD2 by lia. exact E1gp.
  - rewrite U4, OLD3, OLD2 by lia. exact E1tp.
  - reflexivity.
  - rewrite U1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (p1 + (a - p1)) by lia.
    apply (hbb_awr_new HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly1 S1 W1 (ms_mem ms3) md3c 1
      (ablocks B ly2 S2) p1 n (a - p1) ly2 [] HJx1 Hp1n1 Hp1in). lia.
  - intros a Ha _ Hc. exfalso. destruct Hc as [[_ Himg] | Hst]; [pose proof (pa_img_range a Himg); lia | lia].
  - apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms4) md4c p1 n p1 n HAR4 Hp1in); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms4) md4c p1 n p1 n HAR4 Hp1in); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms4) md4c p1 n p1 n HAR4 Hp1in); lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [exact (hbb_astr_some _ s x a Hstr4 ltac:(lia)) | rewrite Hsp4; lia]. }
    split; [exact Hdisj4|]. split; [exact Hamr4|]. split; [exact Hra4' | intros _; exact Hhull4]. }
cbv beta. intros W2x c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4 & _).
cbv beta iota in Heff4.
(* the first copy holds the text *)
assert (Hp1str4 : astr_atR (rdW W2 mem4) p1 x).
{ apply (hbb_astr_move (rdW W2 (ms_mem ms4)) _ s); [|exact Hstr4]. intros i Hi. exact (Heff4 i ltac:(lia)). }
rewrite U1.
jafter_call_keep_pi HS 81%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E3 (w_H W2) (w_H W2) (ms_mem ms4) mem4 2 (spZ regs)); [exact Usp3 | |].
  - intros a Ha. apply Hfr4; lia.
  - intros a Ha. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS U1 U2 U3 U4 U10 U11 U12 U10' U11' U12'.
remember (havoc E3 81 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS5.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall nn, (nn < 81)%nat -> ew E4 nn = ew E3 nn)
  by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE4 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
assert (UHI4 : bv_unsigned (ew E4 (A_HI HBB_ANS_HI)) = A_G_REC + OFF_ANSWER + 0x340)
  by (rewrite (HEI4 (A_HI HBB_ANS_HI) ltac:(unfold A_HI, A_TEXT, A_LIM, HBB_ANS_HI; lia)); exact hbb_val_hi).
(* the region of the store at 0x8a9c8: g_rec.answer, through the auipc atom A_HI 121 *)
pose proof (st_ok_pi_add_region E4 _ _ hbb_store_region HS5 eq_refl) as HS.
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ unfold region_ok, hbb_store_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite UHI4. split; [unfold A_G_REC, OFF_ANSWER; lia|]. split; [unfold A_G_REC, OFF_ANSWER; lia|].
  split; [|constructor].
  intros o Ho. apply PROG_WRITABLE. apply hbb_ans_PG. lia. }
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, hbb_store_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UHI4, Usp4. unfold A_G_REC, OFF_ANSWER. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear HS5. rewrite <- restrict_mkst_fx in HS.
assert (UHI4' : bv_unsigned (ew E4 521%nat) = A_G_REC + OFF_ANSWER + 0x340) by exact UHI4.

(* ==== 0x8a9c8 .. 0x8a9d0: g_rec.answer := the first copy, a0 := text; jal strlen ==== *)
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact UHI4' | | ].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply hbb_awr_ans. unfold A_G_REC, OFF_ANSWER in *. lia.
  - eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
clear HF HG. rename HFr into HFr5. rename ms into ms5.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md5c := mdx) in *; clearbody md5c end.
prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
prreg HS (10%bv : bv 5) V10.
assert (Hsp5 : spZ (ms_regs ms5) = spZ regs + -48) by (unfold spZ at 1; rewrite V2, Usp4; apply unsigned_lit_small; lia).
(* g_rec.answer holds the first copy *)
pose proof (st_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HRg. cbn [ms_mem restrict] in HRg.
pose proof (field_of_region_any E4 _ (A_HI HBB_ANS_HI) (A_G_REC + OFF_ANSWER + 0x340) _ _ _ _ _ (-0x340) 8 (SOff 69 0)
  HRg UHI4 ltac:(cbn; tauto) ltac:(cbn; lia)) as Fans.
assert (Vans5 : aval_mem (rdW W2 (ms_mem ms5)) (A_G_REC + OFF_ANSWER) 8 p1).
{ assert (D69 : bv_unsigned (sv_denot E4 (SOff 69 0)) mod 2 ^ (8 * Z.of_N 8) = p1).
  { cbn [sv_denot]. rewrite OLD4 by lia. rewrite E69, Hp1r, Z.add_0_r. unfold w64.
    rewrite Z_to_bv_bv_unsigned, unsigned_lit_small by lia. apply Z.mod_small. change (8 * Z.of_N 8) with 64. lia. }
  rewrite D69 in Fans. replace (A_G_REC + OFF_ANSWER + 0x340 + -0x340) with (A_G_REC + OFF_ANSWER) in Fans by lia.
  change (N.to_nat 8) with 8%nat in Fans.
  exact (aval_mem_view SEGS (w_H W2) (ms_mem ms5) _ _ _ Fans). }
assert (K5 : forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) ->
  rdW W2 (ms_mem ms5) a = rdW W2 mem4 a).
{ intros a Ha Hna. apply (recb_run_keeps_m (PI := PI) E4 _ (w_H W2) mem4 (ms_mem ms5) a HFr5); [lia|].
  intros (r & Hr & Hw). vm_compute in Hr. unfold A_G_REC, OFF_ANSWER in Hna.
  destruct Hr as [Hr | [Hr | []]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
  - rewrite UHI4' in Hw. unfold A_G_REC, OFF_ANSWER in Hw. lia.
  - rewrite Usp4 in Hw. lia. }
destruct (hbb_src ly S W mem md cid pos s x HAND_BACK_STK (spZ regs) old O ly2 S2 W2 (ms_mem ms5) md5c (1 + EV_XMALLOC)
  HAR HO Hfr Hcid Hfal Hfle Hfhi Hstr Hsra HJ4) as (_ & Hstr5 & Hra5 & Hhull5 & Hamr5 & Htail5).
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms5)))
  by exact (hbb_aro ly S W mem md old O _ _ _ _ _ _ _ _ _ HAR HO HJ4 HROD).
pmkst HS.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ENV ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen) W2
    (ms_regs ms5) (ms_mem ms5) HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly2 S2 md5c (1 + EV_XMALLOC)
    (-48) (getr (ms_regs ms5) 1) (fun regs' _ => getr regs' 10 = w64 (astr_len x)) HJ4).
  - exact Hsp5.
  - reflexivity.
  - lia.
  - lia.
  - rewrite Hes, HBS. lia.
  - reflexivity.
  - intros a [].
  - apply (ASTRLEN fx ly2 S2 W2 (ms_regs ms5) (ms_mem ms5) md5c s x).
    + apply (ecall_pre_stk_at SEGS B ESTACK HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly2 S2 W2
        (ms_mem ms5) md5c (1 + EV_XMALLOC) (ms_regs ms5) (-48) HJ4 Hsp5 eq_refl ltac:(lia) ltac:(lia)
        ltac:(rewrite Hes, HBS; lia)).
      * rewrite V1. apply ret_ok_codeptr_v; [lia | reflexivity].
      * rewrite V3, OLD4, OLD3, OLD2 by lia. exact E1gp.
      * rewrite V4, OLD4, OLD3, OLD2 by lia. exact E1tp.
    + rewrite V10, OLD4, OLD3, OLD2 by lia. exact E1s.
    + lia.
    + apply astr_atR_view. exact Hstr5.
    + rewrite Hlenx. apply (hbb_aread W2 (ms_regs ms5) (ms_mem ms5) s x ESTACK);
      [lia | lia | lia | rewrite Hsp5, Hes; lia | exact Hstr5 | exact Hamr5 | exact Hra5 | exact Hhull5].
    + rewrite Hlenx. exact Htail5.
    + exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W2 (ms_mem ms5) HROD5). }
cbv beta. intros W2y c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HQ5 & HK5).
rewrite V1.
jafter_call_keep_pi HS 97%nat regs5 (mrestrict (w_H W2) mem5) HP5 [1]%nat HS6.
match type of HS6 with ?t -> _ => assert (HRK : t); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E4 (w_H W2) (w_H W2) (ms_mem ms5) mem5 2 (spZ regs)); [exact Usp4 | |].
  - intros a Ha. apply HK5; [lia | lia | intros []].
  - intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS V1 V2 V3 V4 V10 HRg Fans. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc E4 97 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall nn, (nn < 97)%nat -> ew E5 nn = ew E4 nn)
  by (intros nn Hnn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E5)
  by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
assert (E101 : ew E5 101 = getr regs5 10) by (rewrite HE5; reflexivity).
clear HE5.
assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Usp4).

(* ==== 0x8a9d4 .. 0x8a9dc: s1 := |text| + 1, a0 := s1; jal xmalloc ==== *)
paj_run_shc RUNP RUNC HS HJ5.
{ awr_ok_tac. exact Usp5. }
clear HF HG. rename HFr into HFr6. rename ms into ms6. rename HJ5 into HJx2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md6c := mdx) in *; clearbody md6c end.
prreg HS (1%bv : bv 5) Y1. prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3. prreg HS (4%bv : bv 5) Y4.
prreg HS (8%bv : bv 5) Y8. prreg HS (10%bv : bv 5) Y10.
assert (Hsp6 : spZ (ms_regs ms6) = spZ regs + -48) by (unfold spZ at 1; rewrite Y2, Usp5; apply unsigned_lit_small; lia).
assert (Hs06 : s0Z (ms_regs ms6) = s)
  by (unfold s0Z; rewrite Y8, OLD5, OLD4, OLD3, OLD2, E1s by lia; apply unsigned_lit_small; lia).
assert (Y10' : getr (ms_regs ms6) 10 = w64 n).
{ rewrite Y10, E101, HQ5, Hlenx. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (K6 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms6) a = rdW W2 mem5 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E5 _ (w_H W2) mem5 (ms_mem ms6) a HFr6); [lia|].
  intros (r & Hr & Hw). vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?Usp5 in Hw; lia|]).
  destruct Hr. }
assert (Hnev6 : st_nev S2 + EV_XMALLOC <= EV_MAX).
{ pose proof HJx2 as (_ & _ & _ & _ & _ & _ & Hn6 & _). unfold EV_XMALLOC in *. lia. }
assert (Hlive6 : blocks_bytes S2 + LIVE_XMALLOC n <= LIVE_MAX) by (rewrite HLX in HBB3 |- *; lia).
assert (MLE13 : mo_le MT S S2 (mo_free MT + XM_XMALLOC MT n)) by exact (mle_station MT S S1 S2 _ _ MTL MLE1 MLE3).
assert (Hmok6 : mo_ok MT S2 (XM_XMALLOC MT n)).
{ apply (mok_station MT S S2 _ (mo_free MT + XM_XMALLOC MT n) (XM_XMALLOC MT n) MTL HMOKn MLE13); lia. }
pmkst HS. rewrite hbb_sig_xmalloc.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W2 (ms_regs ms6) (ms_mem ms6) _ HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md []
    ly2 S2 md6c (1 + EV_XMALLOC) XMALLOC_STK [] EV_XMALLOC (-48) (getr (ms_regs ms6) 1) [] _ HJx2).
  - exact Hsp6.
  - reflexivity.
  - lia.
  - rewrite HXS. lia.
  - rewrite HXS, HBS. lia.
  - rewrite Y3, OLD5, OLD4, OLD3, OLD2 by lia. exact E1gp.
  - rewrite Y4, OLD5, OLD4, OLD3, OLD2 by lia. exact E1tp.
  - reflexivity.
  - rewrite Y1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Y1, unsigned_lit_small by lia. lia.
  - rewrite Hs06. apply achain_low. lia.
  - intros HPREc. eapply SRr_mono.
    { apply (TXMALLOC fx ly2 S2 W2 (ms_regs ms6) (ms_mem ms6) md6c [] n HPREc Y10').
      - unfold MALLOC_MAX, LMAX in *. lia.
      - exact Hnev6.
      - exact Hlive6.
      - exact Hmok6. }
    intros W3 c6 _ Hc6. exact Hc6.
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta.
intros W3 c6 Hwle6 (ly3 & S3 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 & (p2 & Hp2r & Hp2rng & Hp2perm & Hp2apart & Hp2blk & HBB6 & MLE6)).
rewrite HLX in Hp2perm, Hp2apart, Hp2blk.
assert (KX6p1 : forall i, 0 <= i < n -> rdW W3 mem6 (p1 + i) = rdW W2 (ms_mem ms6) (p1 + i)).
{ intros i Hi. pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2c & _).
  apply (F2c p1 n i Hp1in); [eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | right; exact Hp1in] | lia | apply inFP_nil]. }
assert (KX6ans : forall a, A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8 -> rdW W3 mem6 a = rdW W2 (ms_mem ms6) a).
{ intros a Ha. pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3c & _).
  destruct (cmd_prog_unowned SEGS B LAWS HB IMG a (hbb_ans_PG a Ha)) as (Himg & Hno & Herr).
  apply F3c; [exact Himg | exact Hno | exact Herr |].
  apply fp_spares_closed; [apply sink_closed_pos; apply Forall_nil | apply inFP_nil]. }
rewrite Y1.
jafter_call_keep_pi HS 113%nat regs6 (mrestrict (w_H W3) mem6) HP6 [0]%nat HS7.
match type of HS7 with ?t -> _ => assert (HRK : t); [|specialize (HS7 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E5 (w_H W2) (w_H W3) (ms_mem ms6) mem6 2 (spZ regs)); [exact Usp5 | |].
  - intros a Ha. pose proof HJc6 as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & _).
    apply K9; [lia | rewrite HXS; lia | apply inFP_nil].
  - intros a Ha. pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS Y1 Y2 Y3 Y4 Y8 Y10 Y10'. rewrite <- restrict_mkst_fx in HS7. rename HS7 into HS.
remember (havoc E5 113 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (OLD6 : forall nn, (nn < 113)%nat -> ew E6 nn = ew E5 nn)
  by (intros nn Hnn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E6)
  by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
assert (E117 : ew E6 117 = getr regs6 10) by (rewrite HE6; reflexivity).
clear HE6.
assert (Usp6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Usp5).

(* ==== 0x8a9e0 .. 0x8a9ec: s2 := the second copy, a1 := text, a2 := s1; jal __asan_memcpy ==== *)
paj_run_shc RUNP RUNC HS HJ6.
{ awr_ok_tac. exact Usp6. }
clear HF HG. rename HFr into HFr7. rename ms into ms7.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md7c := mdx) in *; clearbody md7c end.
prreg HS (1%bv : bv 5) Z1. prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4.
prreg HS (10%bv : bv 5) Z10. prreg HS (11%bv : bv 5) Z11. prreg HS (12%bv : bv 5) Z12.
assert (Hsp7 : spZ (ms_regs ms7) = spZ regs + -48) by (unfold spZ at 1; rewrite Z2, Usp6; apply unsigned_lit_small; lia).
assert (Z10' : getr (ms_regs ms7) 10 = w64 p2) by (rewrite Z10, E117; exact Hp2r).
assert (Z11' : getr (ms_regs ms7) 11 = w64 s) by (rewrite Z11, OLD6, OLD5, OLD4, OLD3, OLD2 by lia; exact E1s).
assert (Z12' : getr (ms_regs ms7) 12 = w64 n).
{ rewrite Z12, OLD6, E101, HQ5, Hlenx by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (K7 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem ms7) a = rdW W3 mem6 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E6 _ (w_H W3) mem6 (ms_mem ms7) a HFr7); [lia|].
  intros (r & Hr & Hw). vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?Usp6 in Hw; lia|]).
  destruct Hr. }
pose proof (proj1 HJ6) as HAR7.
pose proof HJ6 as (_ & Hly7 & _ & _ & _ & Hfrs7 & _).
assert (Hp2in : In (p2, n) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hp2perm | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p2 n HAR7 Hp2in) as (_ & Hp24096 & Hp2ceil & _ & _ & _ & _).
pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms7) md7c p2 n HAR7 Hp2in) as Hp2off. unfold off_img in Hp2off.
assert (Hp2n2 : ~ In (p2, n) (ablocks B ly2 S2)) by (apply hbb_apart_notin; [lia | exact Hp2apart]).
assert (Hp12 : p2 + n <= p1 \/ p1 + n <= p2).
{ pose proof (proj1 (Forall_forall _ _) Hp2apart (p1, n) Hp1in) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
destruct (hbb_src ly S W mem md cid pos s x HAND_BACK_STK (spZ regs) old O ly3 S3 W3 (ms_mem ms7) md7c
  (1 + EV_XMALLOC + EV_XMALLOC) HAR HO Hfr Hcid Hfal Hfle Hfhi Hstr Hsra HJ6) as (_ & Hstr7 & Hra7 & Hhull7 & Hamr7 & _).
assert (Hfr3 : In (cid, pos) (frames S3)) by (rewrite Hfrs7; exact Hfr).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR Hly7) as (_ & Efa3 & _).
assert (Hdisj7 : p2 + n <= s \/ s + n <= p2).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms7) md7c p2 n cid pos HAR7 Hp2in Hfr3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa3 in Hd. lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W3 (ms_regs ms7) (ms_mem ms7)
    HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly3 S3 md7c (1 + EV_XMALLOC + EV_XMALLOC) p2 s n (-48)
    (getr (ms_regs ms7) 1) HJ6).
  - exact Z10'.
  - exact Z11'.
  - exact Z12'.
  - unfold LMAX in *. lia.
  - lia.
  - lia.
  - exact Hsp7.
  - reflexivity.
  - lia.
  - rewrite Hes, HBS. lia.
  - rewrite Z3, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact E1gp.
  - rewrite Z4, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. exact E1tp.
  - reflexivity.
  - rewrite Z1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|lia].
    replace a with (p2 + (a - p2)) by lia.
    apply (hbb_awr_new HAND_BACK_STK (spZ regs) (hbb_FP old O) ly S W mem md [] ly2 S2 W2 (ms_mem ms6) md6c
      (1 + EV_XMALLOC) (ablocks B ly3 S3) p2 n (a - p2) ly3 [] HJx2 Hp2n2 Hp2in). lia.
  - intros a Ha _ Hc. exfalso. destruct Hc as [[_ Himg] | Hst]; [pose proof (pa_img_range a Himg); lia | lia].
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms7) md7c p2 n p2 n HAR7 Hp2in); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms7) md7c p2 n p2 n HAR7 Hp2in); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms7) md7c p2 n p2 n HAR7 Hp2in); lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [exact (hbb_astr_some _ s x a Hstr7 ltac:(lia)) | rewrite Hsp7; lia]. }
    split; [exact Hdisj7|]. split; [exact Hamr7|]. split; [exact Hra7 | intros _; exact Hhull7]. }
cbv beta. intros W3x c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Ha07 & Heff7 & Hfr7 & Hpres7 & _).
cbv beta iota in Heff7.
rewrite Z1.
jafter_call_keep_pi HS 129%nat regs7 (mrestrict (w_H W3) mem7) HP7 [0]%nat HS8.
match type of HS8 with ?t -> _ => assert (HRK : t); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply (hbb_region_kept_hi2 SEGS E6 (w_H W3) (w_H W3) (ms_mem ms7) mem7 2 (spZ regs)); [exact Usp6 | |].
  - intros a Ha. apply Hfr7; lia.
  - intros a Ha. pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP14 & _). apply HP14. rewrite HBS. lia. }
clear HS Z1 Z2 Z3 Z4 Z10 Z11 Z12 Z10' Z11' Z12'. rewrite <- restrict_mkst_fx in HS8. rename HS8 into HS.
remember (havoc E6 129 (map (getr regs7) CLOB)) as E7 eqn:HE7 in HS.
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc; [exact HEI6 | cbv; lia]).
assert (OLD7 : forall nn, (nn < 129)%nat -> ew E7 nn = ew E6 nn)
  by (intros nn Hnn; rewrite HE7; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 old]) E7)
  by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
clear HE7.
assert (Usp7 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Usp6).

(* ==== 0x8a9f0 .. 0x8aa0c: a0 := the second copy, the callee-saved registers back, ret ==== *)
paj_run_shc RUNP RUNC HS HJ7.
{ awr_ok_tac. exact Usp7. }
clear HF HG. rename HFr into HFr8. rename ms into ms8.
assert (K8 : forall a, 0 <= a < alloc_ceiling -> rdW W3 (ms_mem ms8) a = rdW W3 mem7 a).
{ intros a Ha. apply (recb_run_keeps_m (PI := PI) E7 _ (w_H W3) mem7 (ms_mem ms8) a HFr8); [lia|].
  intros (r & Hr & Hw). vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite ?Usp7 in Hw; lia|]).
  destruct Hr. }
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matF.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
assert (Hra1' : getr (ms_regs ms8) 1 = getr regs 1)
  by (rewrite F1, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 by lia; exact (EE 1%nat 1%bv eq_refl)).
assert (F10' : getr (ms_regs ms8) 10 = w64 p2) by (rewrite F10, OLD7, E117 by lia; exact Hp2r).
(* what the last steps kept: g_rec.answer, the first copy, and the second copy *)
assert (Vans8 : aval_mem (rdW W3 (ms_mem ms8)) (A_G_REC + OFF_ANSWER) 8 p1).
{ intros kk Hkk.
  set (a := A_G_REC + OFF_ANSWER + Z.of_nat kk).
  assert (Haa : a = A_G_REC + OFF_ANSWER + Z.of_nat kk) by reflexivity.
  assert (Ha : A_G_REC + OFF_ANSWER <= a < A_G_REC + OFF_ANSWER + 8) by lia.
  pose proof (hbb_ans_img a Ha) as Hai.
  rewrite (K8 a ltac:(lia)), (Hfr7 a ltac:(lia) ltac:(lia) ltac:(lia)), (K7 a ltac:(lia)), (KX6ans a Ha),
    (K6 a ltac:(lia)), (HK5 a ltac:(lia) ltac:(lia) ltac:(intros [])).
  exact (Vans5 kk Hkk). }
assert (KP1 : forall i, 0 <= i < n -> rdW W3 (ms_mem ms8) (p1 + i) = rdW W2 mem4 (p1 + i)).
{ intros i Hi. pose proof (KX6p1 i Hi) as Kx.
  set (a := p1 + i) in *.
  assert (Haa : a = p1 + i) by reflexivity.
  rewrite (K8 a ltac:(lia)), (Hfr7 a ltac:(lia) ltac:(lia) ltac:(lia)), (K7 a ltac:(lia)), Kx,
    (K6 a ltac:(lia)), (HK5 a ltac:(lia) ltac:(lia) ltac:(intros [])), (K5 a ltac:(lia) ltac:(unfold A_G_REC, OFF_ANSWER; lia)).
  reflexivity. }
assert (Hp1str8 : astr_atR (rdW W3 (ms_mem ms8)) p1 x).
{ apply (hbb_astr_move (rdW W2 mem4) _ p1); [|exact Hp1str4]. intros i Hi. exact (KP1 i Hi). }
assert (Hp2str8 : astr_atR (rdW W3 (ms_mem ms8)) p2 x).
{ apply (hbb_astr_move (rdW W3 (ms_mem ms7)) _ s); [|exact Hstr7]. intros i Hi.
  rewrite (K8 (p2 + i) ltac:(lia)). exact (Heff7 i Hi). }
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
unfold apost_base. eexists ly3, S3, (ms_regs ms8), (ms_mem ms8), _.
split; [rewrite Hra1', Hra'; reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ7 |
  unfold EV_HAND_BACK, EV_XMALLOC; lia]|].
split; [exact (aregs_preserved_of_st_ok SEGS (w_H W3) E7 _ ms8 regs [Z_to_bv 64 old] HS HAE7 ltac:(vm_compute; reflexivity))|].
exact (hbb_post ly S W mem md R O Q x old ly1 S1 ly2 S2 W2 (ms_mem ms4) md4c ly3 S3 W3 (ms_mem ms8) _
  HAND_BACK_STK (spZ regs) [] _ p1 p2 (ms_regs ms8) HAR HAREP HOQ Hans Hold Hlen HBL1 Hp1perm Hp1apart HAR4
  Hp2perm Hp2apart HJ7 Vans8 Hp1str8 Hp2str8 F10' Hp2rng HBB1 HBB3 HBB6 (mle_station MT S S2 S3 _ _ MTL MLE13 MLE6)).
Qed.
(* the walk's hypotheses: the statement's own (TXMALLOC, AFREE4, AFREE_NULL4, AMEMCPY, ASTRLEN, VOBJS) and the
   Section hypotheses named above (HB, MTL, cmd_val_his_PB, cmd_sig_prog_PB, cmd_img_facts_tfib, cmd_palib, PRW) *)
Print Assumptions thand_back_holds.
End e.
End f.
End d.

Print Assumptions thand_back_holds.
