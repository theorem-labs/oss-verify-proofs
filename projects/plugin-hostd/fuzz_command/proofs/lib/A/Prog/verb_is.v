(* The walk of verb_is on the ASan build of plugin-hostd/fuzz_command (0x8df5c, 30 instructions), in
   cgif_file_fuzzer's walk style: the symbolic executor over the position-abstract listing (lib/A/Prog/CmdList.v) runs
   the prologue to each wrapper call, the call applies its contract (the statement's Section hypotheses STRCSPN /
   STRNCMP) through the kit's aj_art_at (lib/A/Prog/PaArt.v), the state after the call is rebuilt with
   st_ok_pi_after_call_hi, the branch at 0x8df9c is split with paj_branch, and both paths end at the `ret` with
   paj_ret_at.

   tverb_is_spec_proof proves the contract of lib/A/Prog/verb_is_c.v from the statement's premises and the walk's
   record hypotheses: HB : CmdBSyms B, TL : PALib B and IMG : cmd_img_facts SEGS B. The record
   facts it uses are the record's base lemmas over `SEGS B LAWS HB` (LAWS is YG0q.AR_laws_ok):
   CmdRecImg.cmd_heap_tail_vis gives the word tail of the token, a string in a live block;
   CmdRecBase.cmd_aread_ok_chk turns the record's checks cmd_addr_b / cmd_hull_b (lib/A/Prog/CmdChk.v) into
   range_addressable and shadow_hull_vis, for a format in the read-only disjunct of astr_argA
   (lib/A/Prog/CmdRep.v:150-152) and for the separator literals " " 0x22d80 and " \t" 0x224c0, whose checks hold by
   vm_compute; and CmdRecCells.cmd_rec_cells (also over IMG) gives the stack-protector cells
   (aguard_ok 0xa7098 0x6045d8) that the musl body under the strcspn wrapper compares. The runtime entries' ROM
   premise rt_rom_view is the in-segment half of arodata_okP (rom_view_of_aro). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strcspn_c VerbsFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdChk PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecCells CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verb_is_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PCs := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strcspn_c.
Module PVF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.VerbsFacts.
Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* the symbolic state at the entry: the registers as atoms, the 32-byte frame below sp writable *)
Definition ss_vi0 : sstate := mkSS AF_verb_is sr_atoms [stack_region 32] None (mkFacts [] [] []).

Lemma vi_no0 : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun b => bv_unsigned b <> 0) s.
Proof.
intros s H. apply Forall_forall. intros b Hb Hz. apply H.
replace (Z_to_bv 8 0) with b; [exact Hb|]. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* memory below the allocation ceiling unchanged: every write of verb_is and of the wrappers it calls lands in
   the real stack, which is above it *)
Definition kw (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma kw_refl : forall W m, kw W m m.
Proof. intros W m a _. reflexivity. Qed.
Lemma kw_trans : forall W m1 m2 m3, kw W m1 m2 -> kw W m2 m3 -> kw W m1 m3.
Proof. intros W m1 m2 m3 K1 K2 a Ha. rewrite (K2 a Ha). exact (K1 a Ha). Qed.
Lemma kw_of_win : forall W m m' lo hi, alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> kw W m m'.
Proof.
intros W m m' lo hi Hlo H a Ha. pose proof asan_consts as (C1 & _). apply H; lia.
Qed.
Lemma vis_of_abytes : forall W m x l, abytes_at SEGS W m x l ->
forall a, x <= a < x + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m x l H a Ha. specialize (H (Z.to_nat (a - x)) ltac:(lia)).
rewrite Z2Nat.id in H by lia. replace (x + (a - x)) with a in H by lia. rewrite H. discriminate.
Qed.
Lemma abytes_at_kw : forall W m m' x l, abytes_at SEGS W m x l -> 0 <= x ->
x + Z.of_nat (length l) <= alloc_ceiling -> kw W m m' -> abytes_at SEGS W m' x l.
Proof. intros W m m' x l H Hx Hl K i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma astr_at_kw : forall W m m' x s, astr_at SEGS W m x s -> 0 <= x ->
x + Z.of_nat (length s) + 1 <= alloc_ceiling -> kw W m m' -> astr_at SEGS W m' x s.
Proof.
intros W m m' x s [H1 H2] Hx Hl K. split; [|exact H2].
apply (abytes_at_kw W m m' x _ H1 Hx); [rewrite length_app; cbn [length]; lia | exact K].
Qed.
Lemma atail_vis_kw : forall W m m' e, atail_vis SEGS W m e -> 0 <= e < alloc_ceiling -> kw W m m' -> atail_vis SEGS W m' e.
Proof.
intros W m m' e H He K a Ha. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM.
unfold YG0f.ASAN_CEIL in CR, CM.
pose proof (Z.div_mod e 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D2.
rewrite K by lia. exact (H a Ha).
Qed.
Lemma aguard_ok_kw : forall W m m' g gd, aguard_ok SEGS W m g gd -> 0 <= g -> g + 8 <= alloc_ceiling ->
0 <= gd -> gd + 8 <= alloc_ceiling -> kw W m m' -> aguard_ok SEGS W m' g gd.
Proof.
intros W m m' g gd [H1 (c & H2)] Hg1 Hg2 Hd1 Hd2 K. split.
- rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') g); [exact H1|]. intros k Hk. apply K. lia.
- exists c. rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') gd); [exact H2|]. intros k Hk. apply K. lia.
Qed.
Lemma rt_rom_view_kw : forall B W m m', rt_rom_view SEGS B W m -> kw W m m' -> rt_rom_view SEGS B W m'.
Proof.
intros B W m m' H K a Hr Ho He. pose proof asan_consts as (C1 & _).
assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
pose proof (pa_img_range _ Hi) as R.
rewrite K by lia. exact (H a Hr Ho He).
Qed.

(* the range facts an interceptor checks, below the allocation ceiling (RtDefs.v's aread_ok without its window part) *)
Definition rdf (W : world SEGS) (m : word -> option byte) (x n : Z) : Prop :=
0 < x /\ 0 <= n < 2 ^ 32 /\ x + n <= alloc_ceiling /\
(forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None) /\ amem_range x n /\
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma rdf_kw : forall W m m' x n, rdf W m x n -> kw W m m' -> rdf W m' x n.
Proof.
intros W m m' x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) K. pose proof asan_consts as (C1 & C2 & _).
assert (HK : forall s, 0 <= s < 2 ^ 64 -> ~ (alloc_ceiling <= s < 2 ^ 64) -> aview SEGS (w_H W) m' s = aview SEGS (w_H W) m s)
by (intros s Hs Hns; apply K; lia).
split; [exact Hx|]. split; [exact Hn|]. split; [exact Hc|].
split; [intros a Ha; rewrite K by lia; apply Hv; exact Ha|]. split; [exact Ham|].
split; [exact (range_addressable_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hra)|].
intros Hn0. exact (shadow_hull_vis_kept_win _ _ alloc_ceiling (2 ^ 64) x n HK ltac:(lia) ltac:(lia) ltac:(lia) Hn0 (Hh Hn0)).
Qed.
Lemma rdf_sub : forall W m x n k, rdf W m x n -> 0 <= k <= n -> rdf W m x k.
Proof.
intros W m x n k (Hx & Hn & Hc & Hv & Ham & Hra & Hh) Hk.
split; [exact Hx|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hv; lia|].
split; [unfold amem_range in *; lia|]. split; [unfold range_addressable in *; intros y Hy; apply Hra; lia|].
intros Hk0. specialize (Hh ltac:(lia)). unfold shadow_hull_vis in *. intros s Hs. apply Hh.
assert (A1 : shadow_addr (x + k - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : shadow_addr (x + k - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma rdf_aread : forall W m (regs : bvmap 5 word) stk x n, rdf W m x n -> alloc_ceiling <= spZ regs - stk ->
aread_ok SEGS stk W regs m x n.
Proof.
intros W m regs stk x n (Hx & Hn & Hc & Hv & Ham & Hra & Hh) Hs. pose proof asan_consts as (C1 & _).
unfold aread_ok. split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [apply Hv; lia | unfold ascratch_stk; lia]|].
split; [exact Ham|]. split; [exact Hra | exact Hh].
Qed.

Lemma region_kept_win : forall E n lo hi wlo whi cs sp H (m m' : word -> option byte) wl wh,
bv_unsigned (ew E n) = sp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wl <= a < wh) -> aview SEGS H m' a = aview SEGS H m a) ->
wh <= sp + lo -> 0 <= sp + lo -> sp + hi <= 2 ^ 64 ->
(forall a, sp + wlo <= a < sp + whi -> apresent H m' a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E n lo hi wlo whi cs sp H m m' wl wh Hn Hfr Hwh H0 H64 Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; lia.
- intros _. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the walk's record hypotheses (cgif's names); the record facts are the base lemmas of
   CmdRecBase / CmdRecCells / CmdRecImg over them *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let RET := paj_ret_at (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* a read-only byte lies in the image's address range: the first arm of in_roP is a segment of the image
   (pa_img_range), the second the fixed window [CMD_RLO, CMD_RHI) (CmdGlob.v:22-23), inside it by arithmetic; so
   this walk needs no relro_img *)
Lemma ro_img_range : forall a, in_roP SEGS RLO RHI a -> 0x10000 <= a < 0x606000.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- assert (Himg : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]). exact (pa_img_range a Himg).
- unfold CMD_RLO, CMD_RHI in Hr. lia.
Qed.

(* the runtime entries' ROM premise is the in-segment half of arodata_okP *)
Lemma rom_view_of_aro : forall W mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem H a Hr Ho He. exact (H a (or_introl Hr) Ho He). Qed.

Lemma argA_facts : forall ly S W mem md p s,
AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some s) ->
astr_at SEGS W mem p s /\ rdf W mem p (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= LMAX.
Proof.
intros ly S W mem md p s HAR HA. pose proof asan_consts as (C1 & _).
cbn [astr_argA] in HA. destruct HA as (Hp0 & Hs & Hn & HC).
assert (Hst : astr_at SEGS W mem p s) by (apply astr_atR_view; exact Hs).
assert (Hvis : forall a, p <= a < p + (Z.of_nat (length s) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. destruct Hst as [Hb _]. apply (vis_of_abytes W mem p (s ++ [Z_to_bv 8 0]) Hb). rewrite length_app. cbn [length]. lia. }
unfold LMAX in *. split; [exact Hst|]. split; [|lia].
destruct HC as [[(q & k & Hin & Hq & Hqk) _] | (Hro & Hab & Hhb & _)].
- destruct (al_blocks SEGS B LAWS ly S W mem md q k HAR Hin) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hvis|].
split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia | lia].
- destruct (CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md p (Z.of_nat (length s) + 1) HAR Hab Hhb) as [Hra Hhull].
pose proof (ro_img_range _ (proj1 (Hro 0 ltac:(lia)))) as R1.
pose proof (ro_img_range _ (proj1 (Hro (Z.of_nat (length s)) ltac:(lia)))) as R2.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hvis|].
split; [left; unfold kLowMemEnd; lia|]. split; [exact Hra|]. intros _. exact Hhull.
Qed.

(* the `+ 8` band premise of a string argument (RtString.v's strcspn / strncmp): a heap
   string by the kit's amem8_of_blockA (the block law keeps 8 bytes past its end in the band), a read-only one is an
   image range, so amem8_of_low *)
Lemma argA_amem8 : forall ly S W mem md p s,
AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some s) ->
amem_range p (astr_len s + 8).
Proof.
intros ly S W mem md p s HAR HA. cbn [astr_argA] in HA. destruct HA as (_ & _ & _ & [[Hblk _] | (Hro & _)]).
- exact (amem8_of_blockA SEGS B LAWS ly S W mem md p (astr_len s) HAR Hblk ltac:(unfold astr_len; lia)).
- pose proof (ro_img_range _ (proj1 (Hro 0 ltac:(lia)))) as R1.
pose proof (ro_img_range _ (proj1 (Hro (Z.of_nat (length s)) ltac:(lia)))) as R2.
apply amem8_of_low; unfold astr_len, kLowMemEnd; lia.
Qed.

(* the token: a string in a live block (the statement's in_blockA premise); its word tail lies in the block's
   requested range, so cmd_heap_tail_vis gives it *)
Lemma blk_facts : forall ly S W mem md p s,
AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) p (Z.of_nat (length s) + 1) -> astr_atR (rdW W mem) p s ->
Z.of_nat (length s) + 1 <= LMAX + 1 ->
astr_at SEGS W mem p s /\ rdf W mem p (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= LMAX /\
atail_vis SEGS W mem (p + Z.of_nat (length s)).
Proof.
intros ly S W mem md p s HAR (q & k & Hin & Hq & Hqk) Hs Hn. pose proof asan_consts as (C1 & _).
assert (Hst : astr_at SEGS W mem p s) by (apply astr_atR_view; exact Hs).
assert (Hvis : forall a, p <= a < p + (Z.of_nat (length s) + 1) -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. destruct Hst as [Hb _]. apply (vis_of_abytes W mem p (s ++ [Z_to_bv 8 0]) Hb). rewrite length_app. cbn [length]. lia. }
destruct (al_blocks SEGS B LAWS ly S W mem md q k HAR Hin) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hrk].
unfold LMAX in *. split; [exact Hst|]. split; [|split; [lia|]].
- split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hvis|].
split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia]|].
intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md q k); [exact HAR | exact Hin | lia | lia | lia].
- apply (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md q k); [exact HAR | exact Hin | lia].
Qed.

Lemma ro_lits : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x22d80 RO_lit_22d80 /\ abytes_atR rd 0x224c0 RO_lit_224c0.
Proof. intros rd [H _]. unfold cmd_ro_bytes in H. decompose [and] H. split; assumption. Qed.

(* the words after a literal's terminator: cmd_ro_ok carries them (CmdRo.v cmd_ro_tails) *)
Lemma ro_tail : forall W mem e, cmd_ro_ok (rdW W mem) -> existsb (Z.eqb e) cmd_ro_ends = true -> atail_vis SEGS W mem e.
Proof.
intros W mem e [_ HT] Hin a Ha. apply existsb_exists in Hin as (e' & He' & Hq). apply Z.eqb_eq in Hq. subst e'.
exact (HT e He' a Ha).
Qed.

Lemma vi_lit_rdf : forall W mem a l n,
abytes_atR (rdW W mem) a l -> n = Z.of_nat (length l) -> 0 < a -> a + n <= 0x606000 -> 0 < n < 2 ^ 32 ->
range_addressable (rdW W mem) SHADOW_OFF a n -> shadow_hull_vis (rdW W mem) a n -> rdf W mem a n.
Proof.
intros W mem a l n Hb Hn Ha Han Hn0 Hra Hh. pose proof asan_consts as (C1 & _).
apply abytes_atR_view in Hb.
split; [exact Ha|]. split; [lia|]. split; [lia|].
split; [intros x Hx; apply (vis_of_abytes W mem a l Hb); lia|].
split; [left; unfold kLowMemEnd; lia|]. split; [exact Hra | intros _; exact Hh].
Qed.

Lemma vi_obj : forall E a i v, img_env VAL A_LIM E -> cmd_val_objs -> a = A_OBJ i -> (A_TEXT <= a < A_LIM)%nat ->
(i < length cmd_objs)%nat -> nth i cmd_objs 0 = v -> ew E a = Z_to_bv 64 v.
Proof.
intros E a i v HE HV Ha Hr Hi Hv. rewrite (img_env_atomP E a HE Hr). subst a. rewrite (HV i Hi), Hv. reflexivity.
Qed.

Definition vi_post (tb fb : list byte) (ly : alayout) (S : astate) :=
fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
getr regs' 10 = w64 (if PV.verb_is_m tb fb then 1 else 0) /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
ly' = ly /\ S' = S.

(* the memory a run leaves: it writes only the frame [sp0 - 32, sp0), above the allocation ceiling *)
Ltac vi_kw_run HFr Uspx KW0 KWn :=
lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict ?Hx ?m0) (mrestrict _ ?m1) =>
let KR := fresh "KR" in
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < 2 ^ 64) -> aview SEGS Hx m1 a = aview SEGS Hx m0 a)
by (apply (kept_of_frame (segs := SEGS) Ex rsx Hx m0 m1 (fun x => alloc_ceiling <= x < 2 ^ 64) HFr);
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
cbn [base_val] in Hrr; rewrite Uspx in Hrr; split; lia);
pose proof (kw_trans _ _ _ _ KW0 (kw_of_win _ m0 m1 alloc_ceiling (2 ^ 64) (Z.le_refl _) KR)) as KWn; clear KR
end.

(* the state after a wrapper call: st_ok_pi rebuilt over a fresh band of atoms for the clobbered registers, the
   frame kept *)
Ltac vi_after HS K W regs2 mem2 HP2 HFR2 HJ2 Uspx HS2 :=
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2;
let HRK := fresh "HRK" in
match type of HS2 with ?P -> _ => assert (HRK : P) end;
[ cbn [ms_mem restrict]; constructor; [|constructor];
eapply region_kept_win; [exact Uspx | exact HFR2 | lia | lia | lia |];
let a := fresh "a" in let Ha := fresh "Ha" in let Hp := fresh "Hp" in
intros a Ha; pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _); apply Hp; lia
| specialize (HS2 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS2 ].

Lemma verb_is_core : forall ly S W (regs : bvmap 5 word) mem md (t f : Z) (tb fb : list byte),
afn_pre_na SEGS B VERB_IS_STK ly S W regs mem md ->
getr regs 10 = w64 t -> getr regs 11 = w64 f ->
in_blockA (ablocks B ly S) t (Z.of_nat (length tb) + 1) -> astr_atR (rdW W mem) t tb ->
Z.of_nat (length tb) + 1 <= LMAX + 1 ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] f (Some fb) ->
atail_vis SEGS W mem (f + Z.of_nat (length fb)) ->
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_verb_is) regs mem md)
(apost_base SEGS B VERB_IS_STK [] regs ly S W mem md EV_VERB_IS (vi_post tb fb ly S)).
Proof.
intros ly S W regs mem md t f tb fb HPRE H10 H11 HBt HSt HLt HAf TLf HRO HVO HROD.
pose proof (rom_view_of_aro W mem HROD) as ROMV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : VERB_IS_STK = 8224) by reflexivity. assert (HE4 : ESTACK = 4096) by reflexivity.
set (sp0 := spZ regs) in *.
destruct (blk_facts ly S W mem md t tb HAR HBt HSt HLt) as (STt & RDt & Lt & TLt).
destruct (argA_facts ly S W mem md f fb HAR HAf) as (STf & RDf & Lf).
pose proof (argA_amem8 ly S W mem md f fb HAR HAf) as AMf.
pose proof (amem8_of_blockA SEGS B LAWS ly S W mem md t (astr_len tb) HAR HBt ltac:(unfold astr_len; lia)) as AMt.
destruct (ro_lits _ HRO) as [L1 L2].
pose proof (ro_tail W mem 0x22d81 HRO ltac:(vm_compute; reflexivity)) as TL1.
pose proof (ro_tail W mem 0x224c2 HRO ltac:(vm_compute; reflexivity)) as TL2.
assert (STl1 : astr_at SEGS W mem 0x22d80 [Z_to_bv 8 32]).
{ split; [apply abytes_atR_view; exact L1|]. intros [Hq | []]. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq. discriminate Hq. }
assert (STl2 : astr_at SEGS W mem 0x224c0 [Z_to_bv 8 32; Z_to_bv 8 9]).
{ split; [apply abytes_atR_view; exact L2|].
intros [Hq | [Hq | []]]; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq. }
destruct (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG ly S W mem md HAR) as (_ & HAG & _).
destruct (CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md 0x22d80 2 HAR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [RA1 HV1].
destruct (CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md 0x224c0 3 HAR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [RA2 HV2].
assert (RDl1 : rdf W mem 0x22d80 2) by (apply (vi_lit_rdf W mem 0x22d80 RO_lit_22d80 2 L1); [reflexivity | lia | lia | lia | exact RA1 | exact HV1]).
assert (RDl2 : rdf W mem 0x224c0 3) by (apply (vi_lit_rdf W mem 0x224c0 RO_lit_224c0 3 L2); [reflexivity | lia | lia | lia | exact RA2 | exact HV2]).
pose proof RDt as (Ht0 & _ & Htc & _). pose proof RDf as (Hf0 & _ & Hfc & _).
pose proof (PVF.upto_length (fun b => bv_unsigned b =? 32) fb) as Lvf. fold (PV.vfirst fb) in Lvf.
(* the symbolic state at the entry *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_vi0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_verb_is)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_vi0. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn. tauto.
- split; [exact I | split; exact I]. }
clear HE.
pose proof (ajournal_init_na SEGS B VERB_IS_STK [] ly S W regs mem md HPRE) as HJ.
unfold cfg_at. change (w64 (BASE + AF_verb_is)) with (Z_to_bv 64 (BASE + AF_verb_is)).
(* 0x8df5c .. 0x8df84: the prologue, s0 = format, s1 = token, a1 = " " *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. exact Usp. }
vi_kw_run HFr Usp (kw_refl W mem) KWa. clear HF HFr HG.
(* 0x8df84: strcspn(format, " ") *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msA) =>
prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (2%bv : bv 5) R2;
prreg HS (1%bv : bv 5) R1; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
assert (Hsp1 : spZ (ms_regs msA) = sp0 - 32) by (unfold spZ; rewrite R2, Usp; apply unsigned_lit_small; lia);
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERB_IS_STK sp0 [] ly S W mem md [] ly S W (ms_mem msA) _ 0 (ms_regs msA) (-32) HJ
ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
ltac:(rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp) ltac:(rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp)) as HPRE1;
pmkst HS;
eapply SRr_bind;
[ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs msA) (ms_mem msA) VERB_IS_STK sp0 [] ly S W mem md [] ly S _ 0 (-32) _
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCs.cspn_len [Z_to_bv 8 32] fb))) HJ);
[ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
| ] end.
{ cbn [ss_pc setpc].
apply (STRCSPN fx ly S W _ _ _ f 0x22d80 fb [Z_to_bv 8 32]).
- apply (aguard_ok_kw W mem _ _ _ HAG); [lia | lia | lia | lia | exact KWa].
- exact HPRE1.
- rewrite R10, (EE 11%nat 11%bv eq_refl). exact H11.
- rewrite R11. apply (vi_obj E _ 109 0x22d80 HEI HVO); [reflexivity | cbv; lia | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].
- lia. - lia.
- apply (astr_at_kw W mem _ f fb STf); [lia | lia | exact KWa].
- apply (astr_at_kw W mem _ 0x22d80 _ STl1); [lia | cbn; lia | exact KWa].
- apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDf KWa) | lia].
- exact AMf.
- apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDl1 KWa) | lia].
- change (astr_len [Z_to_bv 8 32]) with 1. apply amem8_of_low; [lia | unfold kLowMemEnd; lia].
- apply (atail_vis_kw W mem _ _ TLf); [lia | exact KWa].
- replace (0x22d80 + astr_len [Z_to_bv 8 32]) with 0x22d81 by reflexivity. apply (atail_vis_kw W mem _ _ TL1); [lia | exact KWa].
- exact (rt_rom_view_kw B W mem _ ROMV KWa). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x : False => x)) as HFR2. clear HFR2'.
rewrite PVF.cspn_vfirst in HQ2.
pose proof (kw_trans _ _ _ _ KWa (kw_of_win _ _ _ (sp0 + -32 - 2 * ESTACK) (sp0 + -32) ltac:(lia) HFR2)) as KWb.
vi_after HS 1024%nat W regs2 mem2 HP2 HFR2 HJ2 Usp HS2. clear HS HP2 HFR2 HPRE1 KWa R10 R11 R2 R3 R4 R1 Hsp1.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (HAE1 : env_agree 32 (Ereg regs []) E1) by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (EO1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (A1 : ew E1 1028 = w64 (Z.of_nat (length (PV.vfirst fb)))).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
unfold CLOB. cbn [map nth]. exact HQ2. }
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite EO1 by lia; exact Usp).
clear HE1.
(* 0x8df88 .. 0x8df98: s2 = n, a1 = " \t", a0 = token *)
paj_run_shc RUNP RUNC HS2 HJ2.
{ awr_ok_tac. exact Usp1. }
vi_kw_run HFr Usp1 KWb KWc. clear HF HFr HG.
(* 0x8df98: strcspn(token, " \t") *)
lazymatch type of HS2 with st_ok _ _ ?ssx (restrict _ ?msB) =>
prreg HS2 (10%bv : bv 5) R10; prreg HS2 (11%bv : bv 5) R11; prreg HS2 (2%bv : bv 5) R2;
prreg HS2 (1%bv : bv 5) R1; prreg HS2 (3%bv : bv 5) R3; prreg HS2 (4%bv : bv 5) R4;
assert (Hsp1 : spZ (ms_regs msB) = sp0 - 32) by (unfold spZ; rewrite R2, Usp1; apply unsigned_lit_small; lia);
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERB_IS_STK sp0 [] ly S W mem md [] ly S W (ms_mem msB) _ 0 (ms_regs msB) (-32) HJ2
ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
ltac:(rewrite R3, EO1, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp) ltac:(rewrite R4, EO1, (EE 4%nat 4%bv eq_refl) by lia; exact Htp)) as HPRE1;
pmkst HS2;
eapply SRr_bind;
[ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs msB) (ms_mem msB) VERB_IS_STK sp0 [] ly S W mem md [] ly S _ 0 (-32) _
(fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCs.cspn_len [Z_to_bv 8 32; Z_to_bv 8 9] tb))) HJ2);
[ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
| ] end.
{ cbn [ss_pc setpc].
apply (STRCSPN fx ly S W _ _ _ t 0x224c0 tb [Z_to_bv 8 32; Z_to_bv 8 9]).
- apply (aguard_ok_kw W mem _ _ _ HAG); [lia | lia | lia | lia | exact KWc].
- exact HPRE1.
- rewrite R10, EO1, (EE 10%nat 10%bv eq_refl) by lia. exact H10.
- rewrite R11. apply (vi_obj E1 _ 81 0x224c0 HEI1 HVO); [reflexivity | cbv; lia | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].
- lia. - lia.
- apply (astr_at_kw W mem _ t tb STt); [lia | lia | exact KWc].
- apply (astr_at_kw W mem _ 0x224c0 _ STl2); [lia | cbn; lia | exact KWc].
- apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDt KWc) | lia].
- exact AMt.
- apply rdf_aread; [exact (rdf_kw _ _ _ _ _ RDl2 KWc) | lia].
- change (astr_len [Z_to_bv 8 32; Z_to_bv 8 9]) with 2. apply amem8_of_low; [lia | unfold kLowMemEnd; lia].
- apply (atail_vis_kw W mem _ _ TLt); [lia | exact KWc].
- replace (0x224c0 + astr_len [Z_to_bv 8 32; Z_to_bv 8 9]) with 0x224c2 by reflexivity. apply (atail_vis_kw W mem _ _ TL2); [lia | exact KWc].
- exact (rt_rom_view_kw B W mem _ ROMV KWc). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3 & HFR3').
pose proof (fun a Ha Hn => HFR3' a Ha Hn (fun x : False => x)) as HFR3. clear HFR3'.
change [Z_to_bv 8 32; Z_to_bv 8 9] with (map (Z_to_bv 8) [32; 9]) in HQ3. rewrite PVF.cspn_tfirst in HQ3.
pose proof (kw_trans _ _ _ _ KWc (kw_of_win _ _ _ (sp0 + -32 - 2 * ESTACK) (sp0 + -32) ltac:(lia) HFR3)) as KWd.
vi_after HS2 1040%nat W regs3 mem3 HP3 HFR3 HJ3 Usp1 HS3. clear HS2 HP3 HFR3 HPRE1 KWb KWc R10 R11 R2 R3 R4 R1 Hsp1.
remember (havoc E1 1040 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS3.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (HAE2 : env_agree 32 (Ereg regs []) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
assert (EO2 : forall n, (n < 1040)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (A2 : ew E2 1044 = w64 (Z.of_nat (length (PV.tfirst tb)))).
{ rewrite HE2. change 1044%nat with (1040 + 4)%nat. rewrite (ew_havoc_new E1 1040 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
unfold CLOB. cbn [map nth]. exact HQ3. }
assert (A1' : ew E2 1028 = w64 (Z.of_nat (length (PV.vfirst fb)))) by (rewrite EO2 by lia; exact A1).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite EO2 by lia; exact Usp1).
clear HE2.
pose proof (PVF.upto_length PV.is_sep tb) as Ltf. fold (PV.tfirst tb) in Ltf.
(* 0x8df9c: bne a0, s2 *)
psrr_branch_pi RUNP BR HS3.
- (* the first-word lengths differ: a0 = 0 *)
rewrite branch_ne_U in Hc.
rewrite (U_atom E2 1044 _ A2), (U_atom E2 1028 _ A1') in Hc by lia.
assert (Hne : length (PV.tfirst tb) <> length (PV.vfirst fb)) by (intros Heq; rewrite Heq, Z.eqb_refl in Hc; discriminate Hc).
paj_run_sh RUNP HS3 HJ3.
{ awr_ok_tac. exact Usp2. }
clear HF HFr HG.
prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (1%bv : bv 5) Q1.
eapply (RET W _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite Q1, EO2, EO1, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS3); [exact HAE2 | vm_compute; reflexivity]|].
unfold vi_post. split; [|split; [apply Permutation_refl | split; reflexivity]].
cbn [ms_regs]. rewrite Q10, (PVF.verb_is_m_len_ne tb fb Hne). reflexivity.
- (* the first-word lengths agree: strncmp(token, format, n) *)
rewrite branch_ne_U in Hc.
rewrite (U_atom E2 1044 _ A2), (U_atom E2 1028 _ A1') in Hc by lia.
assert (Heq : length (PV.tfirst tb) = length (PV.vfirst fb)).
{ destruct (Z.eqb_spec (Z.of_nat (length (PV.tfirst tb))) (Z.of_nat (length (PV.vfirst fb)))) as [Hq | Hq]; [lia | discriminate Hc]. }
paj_run_shc RUNP RUNC HS3 HJ3.
{ awr_ok_tac. exact Usp2. }
vi_kw_run HFr Usp2 KWd KWe. clear HF HFr HG.
set (n1 := Z.of_nat (length (PV.vfirst fb))) in *.
lazymatch type of HS3 with st_ok _ _ ?ssx (restrict _ ?msC) =>
prreg HS3 (10%bv : bv 5) R10; prreg HS3 (11%bv : bv 5) R11; prreg HS3 (12%bv : bv 5) Ra2; prreg HS3 (2%bv : bv 5) R2;
prreg HS3 (1%bv : bv 5) R1; prreg HS3 (3%bv : bv 5) R3; prreg HS3 (4%bv : bv 5) R4;
assert (Hsp1 : spZ (ms_regs msC) = sp0 - 32) by (unfold spZ; rewrite R2, Usp2; apply unsigned_lit_small; lia);
pose proof (ecall_pre_stk_at SEGS B (2 * ESTACK) VERB_IS_STK sp0 [] ly S W mem md [] ly S W (ms_mem msC) _ 0 (ms_regs msC) (-32) HJ3
ltac:(rewrite Hsp1; lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])
ltac:(rewrite R3, EO2, EO1, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp)
ltac:(rewrite R4, EO2, EO1, (EE 4%nat 4%bv eq_refl) by lia; exact Htp)) as HPRE1;
pmkst HS3;
eapply SRr_bind;
[ eapply (ART (2 * ESTACK) (fun _ => False) _ W (ms_regs msC) (ms_mem msC) VERB_IS_STK sp0 [] ly S W mem md [] ly S _ 0 (-32) _
(fun regs' _ => getr regs' 10 = w64 0 <->
StrFun.strncmp_model (tb ++ [Z_to_bv 8 0]) (fb ++ [Z_to_bv 8 0]) n1 = Some 0) HJ3);
[ rewrite Hsp1; lia | reflexivity | lia | lia | lia | exact R1 | intros a [] | ]
| ] end.
{ cbn [ss_pc setpc].
apply (STRNCMP fx ly S W _ _ _ t f n1 tb fb).
- exact HPRE1.
- rewrite R10, EO2, EO1, (EE 10%nat 10%bv eq_refl) by lia. exact H10.
- rewrite R11, EO2, EO1, (EE 11%nat 11%bv eq_refl) by lia. exact H11.
- rewrite Ra2, EO2 by lia. exact A1.
- unfold n1. unfold LMAX in Lf. lia. - lia. - lia.
- apply (astr_at_kw W mem _ t tb STt); [lia | lia | exact KWe].
- apply (astr_at_kw W mem _ f fb STf); [lia | lia | exact KWe].
- apply rdf_aread; [| lia]. apply (rdf_sub _ _ _ (Z.of_nat (length tb) + 1)); [exact (rdf_kw _ _ _ _ _ RDt KWe) | unfold astr_len; lia].
- exact AMt.
- apply rdf_aread; [| lia]. apply (rdf_sub _ _ _ (Z.of_nat (length fb) + 1)); [exact (rdf_kw _ _ _ _ _ RDf KWe) | unfold astr_len; lia].
- exact AMf.
- apply (atail_vis_kw W mem _ _ TLt); [lia | exact KWe].
- apply (atail_vis_kw W mem _ _ TLf); [lia | exact KWe].
- exact (rt_rom_view_kw B W mem _ ROMV KWe). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HQ4 & HFR4').
pose proof (fun a Ha Hn => HFR4' a Ha Hn (fun x : False => x)) as HFR4. clear HFR4'.
vi_after HS3 1056%nat W regs4 mem4 HP4 HFR4 HJ4 Usp2 HS4. clear HS3 HP4 HFR4 HPRE1 R10 R11 Ra2 R2 R3 R4 R1 Hsp1.
remember (havoc E2 1056 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS4.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (HAE3 : env_agree 32 (Ereg regs []) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (EO3 : forall n, (n < 1056)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (A3 : ew E3 1060 = getr regs4 10).
{ rewrite HE3. change 1060%nat with (1056 + 4)%nat. rewrite (ew_havoc_new E2 1056 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
unfold CLOB. cbn [map nth]. reflexivity. }
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite EO3 by lia; exact Usp2).
clear HE3.
(* 0x8dfb0: a0 = (strncmp(..) == 0), the epilogue, ret *)
paj_run_sh RUNP HS4 HJ4.
{ awr_ok_tac. exact Usp3. }
clear HF HFr HG.
prreg HS4 (1%bv : bv 5) Q1.
lazymatch type of HS4 with st_ok_pi _ _ _ ?ssx (restrict _ ?msE) =>
pose proof (st_ok_pi_restrict_reg (w_H W) E3 ssx msE 10%bv HS4) as Q10;
let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in Q10 end.
cbn [ms_regs restrict mkst] in Q10.
destruct (PVF.strncmp_verb tb fb [] (vi_no0 tb (proj2 STt)) (vi_no0 fb (proj2 STf)) Heq) as (v & Hv & Rv & Hv0).
fold n1 in Hv.
eapply (RET W _ _ _ _ _ HS4 eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [cbn [ms_regs]; rewrite Q1, EO3, EO2, EO1, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ4|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS4); [exact HAE3 | vm_compute; reflexivity]|].
unfold vi_post. split; [|split; [apply Permutation_refl | split; reflexivity]].
pose proof (bv_unsigned_in_range 64 (getr regs4 10)) as HR. change (bv_modulus 64) with (2 ^ 64) in HR.
assert (A3' : ew E3 1060 = Z_to_bv 64 (bv_unsigned (getr regs4 10))) by (rewrite A3; symmetry; apply Z_to_bv_bv_unsigned).
cbn [ms_regs]. rewrite Q10. rewrite denot_lit_U.
rewrite U_SAlu, U_SLit, (U_atom E3 1060 _ A3') by lia.
cbn [zalu_raw]. rewrite (YP0m.zcanon_small 1) by lia.
rewrite <- Hv0.
destruct (Z.eqb_spec v 0) as [Hv1 | Hv1].
+ subst v. assert (Hz : getr regs4 10 = w64 0) by (apply HQ4; exact Hv).
rewrite Hz. reflexivity.
+ assert (Hz : bv_unsigned (getr regs4 10) <> 0).
{ intros Hz. apply Hv1. assert (Hw : getr regs4 10 = w64 0) by (unfold w64; rewrite <- Hz; symmetry; apply Z_to_bv_bv_unsigned).
apply HQ4 in Hw. rewrite Hv in Hw. injection Hw as Hw. exact Hw. }
destruct (Z.ltb_spec (bv_unsigned (getr regs4 10)) 1) as [Hl | Hl]; [lia|]. reflexivity.
Qed.

Theorem tverb_is_spec_proof : tverb_is_spec B MT.
Proof.
intros ly S W regs mem md t f tb fb HPRE HROD H10 _ H11 _ HBt HSt HLt HAf TLf HRO HVO _.
exact (verb_is_core ly S W regs mem md t f tb fb HPRE H10 H11 HBt HSt HLt HAf TLf HRO HVO HROD).
Qed.

End e.
End f.
End d.
