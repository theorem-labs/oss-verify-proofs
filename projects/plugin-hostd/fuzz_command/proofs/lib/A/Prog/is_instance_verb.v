(* The walk of is_instance_verb on the ASan build of plugin-hostd/fuzz_command, in cgif_file_fuzzer's style: the
   verified symbolic executor over the position-abstract listing (lib/A/Prog/CmdPaLib.v paj_run / paj_run_to /
   paj_branch over sym_runN_pi_tok), the two interceptor calls through lib/A/Prog/PaArt.v aj_art_at applying
   their contracts (lib/A/Rt/RtString.v astrcspn_realizes / astrncmp_realizes), and the 18 passes of the loop by
   induction on the passes left, from a concrete invariant at the loop header, as cgif's tcbb_loopX does
   (lib/A/AC8b.v:50-255).

   The inline check of the table load (0x8e850) reads its shadow byte through s6, which the compiler steps by 1 per
   pass instead of recomputing (a >> 3) + SHADOW_OFF, so the token engine's check recogniser (lib/Reusable/YCbn.v
   match_x) does not see it as a check. The walk seeds each pass with the table slot and its shadow byte as two
   one-chunk read-only regions based on s5 and s6 (cgif carries its constant cell the same way, bcell_regionP,
   lib/A/Prog/CmdPaLib.v:314): the check becomes an ordinary load of a byte that is 0.

   Proves tis_instance_verb_spec of lib/A/Prog/is_instance_verb_c.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strcspn_c VerbsFacts RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaShadow PaRun PaJournal PaCall PaArt PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdObj CmdRo CmdBase CmdRep CmdZsh CmdChk PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecCells CmdRecImg PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import is_instance_verb_s1 is_instance_verb_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the shadow byte of the table's first granule: SHADOW_OFF + 0xa61a0 / 8 *)
Definition A_SHB : Z := 0x8000cc34.
Definition iiv_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
(* no shadow entries for the engine: the walk's only inline check is a region load, see above *)
Definition iiv_Bx : sv := SLit 0.
Definition iiv_Bspan : Z * Z := (0, 0).
Definition iiv_SH : list shent := [].
Definition iiv_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition iiv_fchunks : list YP09.chunk :=
[YP09.mkChunk 72 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 34 0));
 YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0));
 YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 8 (CVal 8 (SOff 40 0))].
Definition iiv_rstack : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0 iiv_fchunks.
Definition iiv_rslot : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 41 0))].
Definition iiv_rshb : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition iiv_ss_loop : sstate := mkSS IIV_LOOP sr_atoms [iiv_rstack; iiv_rslot; iiv_rshb] None iiv_facts.
Definition iiv_ss_step : sstate := mkSS IIV_STEP sr_atoms [iiv_rstack] None iiv_facts.
Definition iiv_estack : YP09.region := YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [].
Definition iiv_ss_entry : sstate :=
mkSS IIV_ENTRY sr_atoms [iiv_estack; got_regionP; bcell_regionP 32] None iiv_facts.

Lemma iiv_wrap_add : forall v c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + c) = Z_to_bv 64 (v + c).
Proof.
intros v c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Zplus_mod v c), (Zplus_mod (v mod 2 ^ 64) c), Z.mod_mod by lia. reflexivity.
Qed.

Lemma iiv_negmod : forall m, 0 < m < 2 ^ 64 -> (- m) mod 2 ^ 64 = 2 ^ 64 - m.
Proof.
intros m Hm. replace (- m) with (2 ^ 64 - m + (-1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma iiv_U : forall E m c v, ew E m = Z_to_bv 64 v -> U E (SOff m c) = (v + c) mod 2 ^ 64.
Proof.
intros E m c v H. rewrite U_SOff, H, Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* the back edge `bne s4, s7` after pass n: s4 = -8 (n + 1), s7 = -144 *)
Lemma iiv_back : forall n, 0 <= n <= 17 ->
((- (8 * n) + -8) mod 2 ^ 64 =? (-144 + 0) mod 2 ^ 64) = (n =? 17).
Proof.
intros n Hn. replace (- (8 * n) + -8) with (- (8 * n + 8)) by lia.
rewrite (iiv_negmod (8 * n + 8)) by lia. replace ((-144 + 0) mod 2 ^ 64) with (2 ^ 64 - 144) by reflexivity.
destruct (Z.eqb_spec n 17); [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma iiv_aregs : forall (regs' regs0 : bvmap 5 word),
getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
(forall r, 8 <= r <= 9 \/ 18 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
aregs_preserved regs0 regs'.
Proof.
intros regs' regs0 H2 H3 H4 Hs r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact H2 | exact H3 | exact H4 | apply Hs; lia | apply Hs; lia | apply Hs; lia].
Qed.

(* every region of the walk's states after the prologue is read-only (an empty write window) *)
Ltac iiv_awr :=
unfold iiv_ss_step, iiv_ss_loop, iiv_ss_entry; cbn [ss_mem];
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac iiv_sreg HS :=
first [rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS) | rewrite (st_ok_restrict_reg _ _ _ _ _ _ HS)]; cbn [ms_regs restrict];
lazymatch goal with |- context [sv_denot _ (sr_get ?a ?rr2)] =>
let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
(* the statement pins the read-only window (CmdGlob.v:22-23) and names the meter to keep the signature uniform;
   this function reaches neither the allocator nor a side-stack entry, so MT appears only in the spec's name *)
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* The record hypotheses this walk needs and the statement does not carry: HB, TL and IMG. The
   record facts are base lemmas over `SEGS B LAWS HB` (CmdRecFacts.v): the 20 image ranges the two
   wrappers read (the two separator strings and the 18 format literals, 19 of them with a partial last granule,
   which CmdZsh.v's cmd_addressable_in does not reach) come from CmdRecBase.cmd_aread_ok_chk, whose two boolean
   checkers compute to true for every one of them (iiv_img_ok); the token's word tail (a heap string: its last word
   reaches past the terminator, inside its block's requested size) from CmdRecImg.cmd_heap_tail_vis; the
   stack-protector cells the musl body under the strcspn wrapper compares from CmdRecCells.cmd_rec_cells, over IMG
   as well (the pinned image gives IMG, CmdRecImg.v cmd_img_facts_tfib). *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis STRCSPN : forall fx0 : YK11.FPState, @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* a read-only byte of the image lies in the image: the first arm is a segment of it, the second is the fixed
   window [CMD_RLO, CMD_RHI), inside it by computation — so this walk needs no relro_img *)
Lemma iiv_ro_img : forall a, in_roP SEGS RLO RHI a -> 0x10000 <= a < 0x606000.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- assert (Himg : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]). exact (pa_img_range a Himg).
- unfold CMD_RLO, CMD_RHI in Hr. lia.
Qed.

(* the shadow of the 20 ranges the wrappers read: the record's two checkers, by computation *)
Lemma iiv_img_ok : forall ly S (W : world SEGS) mem md a nn, AR SEGS B ly S W mem md ->
In (a, nn) iiv_ro_ranges ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a nn /\ shadow_hull_vis (aview SEGS (w_H W) mem) a nn.
Proof.
intros ly S W mem md a nn HAR Hin.
assert (HC : forallb (fun p => cmd_addr_b (fst p) (snd p) && cmd_hull_b (fst p) (snd p)) iiv_ro_ranges = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in HC. specialize (HC (a, nn) Hin). cbn [fst snd] in HC.
apply andb_prop in HC as [HA HH].
exact (CmdRecBase.cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md a nn HAR HA HH).
Qed.

(* the shadow of g_instance_verbs [0xa61a0, +144) is zero: the table is a range of the record (AF0m.v's
   Tfib_zero_shadow), CmdZsh.v's cmd_zshadow_rec *)
Lemma iiv_tab_zero : forall ly S (W : world SEGS) mem md j, AR SEGS B ly S W mem md -> 0 <= j < 18 ->
aview SEGS (w_H W) mem (A_SHB + j) = Some 0.
Proof.
intros ly S W mem md j HAR Hj.
assert (Hin : In (0xa61a0, 0x90) Tfib_zero_shadow).
{ unfold Tfib_zero_shadow. repeat (first [left; reflexivity | right]). }
pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md (0xa61a0, 0x90) HAR Hin j) as Z.
unfold shadow_of_addr in Z. cbn [fst snd] in Z. apply Z. change (0x90 / 8) with 18. lia.
Qed.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the ROM view the runtime entries take is the statement's arodata_okP read on the ROM segments *)
Lemma iiv_romv : forall (W : world SEGS) mem,
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem H a Hr Ho He. apply H; [left; exact Hr | exact Ho | exact He]. Qed.

Definition iiv_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error iiv_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* the read-only bytes the walk reads and the word tails its wrappers' loops read, the part of cmd_ro_ok this
   function uses; carried across a call by kept_out, as cmd_ro_ok itself (a conjunction over every read-only
   object of the image) is not *)
Definition iiv_roF (W : world SEGS) (mem1 : word -> option byte) : Prop :=
abytes_atR (aview SEGS (w_H W) mem1) A_TAB RO_g_instance_verbs /\
abytes_atR (aview SEGS (w_H W) mem1) A_SEPS RO_lit_224c0 /\
abytes_atR (aview SEGS (w_H W) mem1) A_SP RO_lit_22d80 /\
(forall j, (j < 18)%nat -> abytes_atR (aview SEGS (w_H W) mem1) (iiv_addr j) (nth j iiv_lits [])) /\
(forall j, (j < 18)%nat -> atail_vis SEGS W mem1 (iiv_addr j + Z.of_nat (length (iiv_fmt j)))) /\
atail_vis SEGS W mem1 (A_SEPS + 2) /\ atail_vis SEGS W mem1 (A_SP + 1).

(* the memory facts the walk reads at every call, all outside the window the calls write; t is the token *)
Definition iiv_memF (W : world SEGS) (mem1 : word -> option byte) (sp0 t : Z) (tb : list byte)
(regs0 : bvmap 5 word) : Prop :=
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem1) /\
iiv_roF W mem1 /\
aguard_ok SEGS W mem1 0xa7098 0x6045d8 /\
astr_atR (aview SEGS (w_H W) mem1) t tb /\
t + Z.of_nat (length tb) + 1 <= alloc_ceiling /\
(forall rq, spZ rq = sp0 - 80 -> aread_ok SEGS (2 * ESTACK) W rq mem1 t (Z.of_nat (length tb) + 1)) /\
atail_vis SEGS W mem1 (t + Z.of_nat (length tb)) /\
iiv_frame (mrestrict (w_H W) mem1) sp0 regs0.

Definition iiv_inv (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
(sp0 t : Z) (tb : list byte) (regs0 : bvmap 5 word)
(n : Z) (regs : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
0 <= n <= 17 /\
ajournal SEGS B IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W mem1 md1 0 /\
iiv_memF W mem1 sp0 t tb regs0 /\
spZ regs = sp0 - 80 /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 t /\ getr regs 9 = w64 (Z.of_nat (length (tfirst tb))) /\
getr regs 18 = w64 A_SP /\ getr regs 20 = w64 (- (8 * n)) /\
getr regs 21 = w64 (A_TAB + 8 * n) /\ getr regs 22 = w64 (A_SHB + n) /\ getr regs 23 = w64 (-144) /\
(forall r, 24 <= r <= 27 -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
existsb (verb_is_m tb) (firstn (Z.to_nat n) Lit.instance_verb_formats) = false.

Definition iiv_post (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
(sp0 : Z) (tb : list byte) (regs0 : bvmap 5 word) : world SEGS -> config -> Prop :=
fun W' c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs0 regs' /\
getr regs' 10 = w64 (if existsb (verb_is_m tb) Lit.instance_verb_formats then 1 else 0).

Definition iiv_fixed (regs0 : bvmap 5 word) (sp0 t : Z) (tb : list byte) : Prop :=
cmd_val_objs /\ Forall (fun b : byte => bv_unsigned b <> 0) tb /\ 0 < t /\
Z.of_nat (length tb) + 1 < 2 ^ 32 /\
YK0s.ret_ok (getr regs0 1) /\ getr regs0 2 = w64 sp0 /\
getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\
(* 8 bytes of band room past the token: the string entries' `+ 8` premise (RtString.v:127-131, :164-165) *)
amem_range t (astr_len tb + 8).

Lemma val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (aview SEGS (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

Definition iiv_extra (regs0 : bvmap 5 word) (n : Z) : list word :=
map (fun r => getr regs0 (Z_to_bv 5 r)) iiv_saved ++ [Z_to_bv 64 (iiv_addr (Z.to_nat n))].

Lemma iiv_extra_old : forall (regs0 : bvmap 5 word) n j, (j < 9)%nat ->
nth j (iiv_extra regs0 n) (Z_to_bv 64 0) = getr regs0 (Z_to_bv 5 (nth j iiv_saved 0)).
Proof.
intros regs0 n j Hj. unfold iiv_extra.
rewrite app_nth1 by (rewrite length_map; cbn [length iiv_saved]; lia).
rewrite (nth_indep _ _ (getr regs0 (Z_to_bv 5 0))) by (rewrite length_map; cbn [length iiv_saved]; lia).
apply (map_nth (fun r => getr regs0 (Z_to_bv 5 r)) iiv_saved 0 j).
Qed.

Lemma iiv_extra_fmt : forall (regs0 : bvmap 5 word) n,
nth 9 (iiv_extra regs0 n) (Z_to_bv 64 0) = Z_to_bv 64 (iiv_addr (Z.to_nat n)).
Proof. intros regs0 n. unfold iiv_extra. cbn [map iiv_saved app nth]. reflexivity. Qed.

Lemma iiv_frame_chunks_ok : forall E (m : word -> option byte) sp0 (regs0 : bvmap 5 word),
(forall j, (j < 9)%nat -> ew E (32 + j)%nat = getr regs0 (Z_to_bv 5 (nth j iiv_saved 0))) ->
bv_unsigned (ew E 2) = sp0 - 80 ->
iiv_frame m sp0 regs0 ->
Forall (YP09.chunk_ok SEGS E m (sp0 - 80)) iiv_fchunks.
Proof.
intros E m sp0 regs0 HE Hsp HFR.
assert (CH : forall j, (j < 9)%nat ->
YP09.chunk_ok SEGS E m (sp0 - 80) (YP09.mkChunk (72 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j)%nat 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E m (sp0 - 80) (72 - 8 * Z.of_nat j) 8 (SOff (32 + j)%nat 0)
  (bv_unsigned (getr regs0 (Z_to_bv 5 (nth j iiv_saved 0))))).
  - cbn [sv_denot]. rewrite (HE j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - exact (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth j iiv_saved 0)))).
  - cbn. lia.
  - replace (sp0 - 80 + (72 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
    apply HFR. do 9 (destruct j as [|j]; [reflexivity|]). cbn in Hj. lia. }
unfold iiv_fchunks. repeat apply Forall_cons; try apply Forall_nil.
exact (CH 0%nat ltac:(lia)). exact (CH 1%nat ltac:(lia)). exact (CH 2%nat ltac:(lia)).
exact (CH 3%nat ltac:(lia)). exact (CH 4%nat ltac:(lia)). exact (CH 5%nat ltac:(lia)).
exact (CH 6%nat ltac:(lia)). exact (CH 7%nat ltac:(lia)). exact (CH 8%nat ltac:(lia)).
Qed.
(* the symbolic state at the loop header of pass n: the caller's frame, the table slot the pass loads and the
   shadow byte its inline check reads, all three read-only regions *)
Lemma iiv_seed_loop : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem1 ly S md1 sp0 n,
AR SEGS B ly S W mem1 md1 ->
astk_ok IS_INSTANCE_VERB_STK ly sp0 ->
0 <= n < 18 ->
abytes_atR (aview SEGS (w_H W) mem1) A_TAB RO_g_instance_verbs ->
iiv_frame (mrestrict (w_H W) mem1) sp0 regs0 ->
spZ regs = sp0 - 80 ->
getr regs 21 = w64 (A_TAB + 8 * n) -> getr regs 22 = w64 (A_SHB + n) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (iiv_extra regs0 n))) iiv_ss_loop
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + IIV_LOOP)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS iiv_Bx iiv_SH (Eimg (Ereg regs (iiv_extra regs0 n))) (mrestrict (w_H W) mem1).
Proof.
intros W regs regs0 mem1 ly S md1 sp0 n HAR Hstk Hn HRO HFR Hsp H21 H22.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
set (E := Eimg (Ereg regs (iiv_extra regs0 n))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (iiv_extra regs0 n) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (E21 : bv_unsigned (ew E 21) = A_TAB + 8 * n).
{ rewrite (EE 21%nat 21%bv eq_refl), H21. unfold w64. apply unsigned_lit_small. unfold A_TAB. lia. }
assert (E22 : bv_unsigned (ew E 22) = A_SHB + n).
{ rewrite (EE 22%nat 22%bv eq_refl), H22. unfold w64. apply unsigned_lit_small. unfold A_SHB. lia. }
assert (E41 : ew E 41 = Z_to_bv 64 (iiv_addr (Z.to_nat n))).
{ change 41%nat with (32 + 9)%nat. rewrite EX by lia. apply iiv_extra_fmt. }
split; [|constructor].
rewrite restrict_mkst_fx. unfold iiv_ss_loop. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, iiv_rstack, iiv_rslot, iiv_rshb;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply (iiv_frame_chunks_ok E _ sp0 regs0);
    [intros j Hj; rewrite EX by lia; apply iiv_extra_old; exact Hj | exact E2 | exact HFR].
  + rewrite E21. unfold A_TAB. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (0xa61a0 + 8 * n) 0 8 (SOff 41 0) (iiv_addr (Z.to_nat n))).
    * cbn [sv_denot]. rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * assert (HN18 : (Z.to_nat n < 18)%nat) by lia.
      destruct (iiv_addr_range (Z.to_nat n) HN18) as [Ha1 Ha2].
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * change (Z.of_N 8) with 8. lia.
    * rewrite Z.add_0_r. apply val_mem_of_aval.
      replace (0xa61a0 + 8 * n) with (A_TAB + 8 * Z.of_nat (Z.to_nat n)) by (unfold A_TAB; lia).
      apply (iiv_tab_word _ HRO). lia.
  + rewrite E22. unfold A_SHB. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (0x8000cc34 + n) 0 1 (SLit 0) 0);
    [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | change (Z.of_N 1) with 1; lia |].
    rewrite Z.add_0_r. apply val_mem_of_aval. intros kk Hkk.
    destruct kk as [|kk]; [|cbn in Hkk; lia]. rewrite Z.add_0_r.
    replace (le_byte 0 1 0) with 0 by reflexivity.
    exact (iiv_tab_zero ly S W mem1 md1 n HAR ltac:(lia)).
- apply pairwise_disjoint_of_extents. unfold iiv_rstack, iiv_rslot, iiv_rshb, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite E2, E21, E22.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_TAB, A_SHB. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok iiv_facts]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  split; [lia|]. split; [|lia].
  change (2 ^ 4) with 16. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16.
Qed.


(* the same state at the step block, where only the caller's frame is read *)
Lemma iiv_seed_step : forall (W : world SEGS) (regs regs0 : bvmap 5 word) mem1 ly S md1 sp0 n,
AR SEGS B ly S W mem1 md1 ->
astk_ok IS_INSTANCE_VERB_STK ly sp0 ->
iiv_frame (mrestrict (w_H W) mem1) sp0 regs0 ->
spZ regs = sp0 - 80 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (iiv_extra regs0 n))) iiv_ss_step
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + IIV_STEP)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS iiv_Bx iiv_SH (Eimg (Ereg regs (iiv_extra regs0 n))) (mrestrict (w_H W) mem1).
Proof.
intros W regs regs0 mem1 ly S md1 sp0 n HAR Hstk HFR Hsp.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
set (E := Eimg (Ereg regs (iiv_extra regs0 n))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (iiv_extra regs0 n) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
split; [|constructor].
rewrite restrict_mkst_fx. unfold iiv_ss_step. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, iiv_rstack;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply (iiv_frame_chunks_ok E _ sp0 regs0);
  [intros j Hj; rewrite EX by lia; apply iiv_extra_old; exact Hj | exact E2 | exact HFR].
- apply pairwise_disjoint_of_extents. unfold iiv_rstack, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok iiv_facts]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  split; [lia|]. split; [|lia].
  change (2 ^ 4) with 16. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16.
Qed.

(* every byte this walk reads outside its frame lies in the low image or in a live block, below the window
   [sp0 - 80 - 2 * ESTACK, sp0 - 80) the calls write; the caller's frame lies above it *)
Lemma iiv_roF_of_ro : forall (W : world SEGS) mem1,
cmd_ro_ok (aview SEGS (w_H W) mem1) -> iiv_roF W mem1.
Proof.
intros W mem1 HRO.
destruct (iiv_ro_facts _ HRO) as (HT & HS1 & HS2 & HL & HTl).
split; [exact HT|]. split; [exact HS1|]. split; [exact HS2|]. split; [exact HL|].
split; [|split].
- intros j Hj a Ha. exact (HTl _ (iiv_tail_in j Hj) a Ha).
- intros a Ha. exact (HTl _ iiv_seps_tail_in a Ha).
- intros a Ha. exact (HTl _ iiv_sp_tail_in a Ha).
Qed.

Lemma iiv_roF_kept : forall (W : world SEGS) mem1 mem2 lo hi,
kept_out (aview SEGS (w_H W) mem1) (aview SEGS (w_H W) mem2) lo hi ->
0x606010 <= lo -> lo < 2 ^ 64 -> iiv_roF W mem1 -> iiv_roF W mem2.
Proof.
intros W mem1 mem2 lo hi HK Hlo Hlo2 (HT & HS1 & HS2 & HL & HTl & HE1 & HE2).
assert (HTV : forall e, 0 <= e < 0x606000 -> atail_vis SEGS W mem1 e -> atail_vis SEGS W mem2 e).
{ intros e He Hv. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  eapply (atail_vis_kept SEGS W mem1 mem2 lo hi e HK Hv); lia. }
assert (HBY : forall p l, 0 <= p -> p + Z.of_nat (length l) <= 0x606000 ->
abytes_atR (aview SEGS (w_H W) mem1) p l -> abytes_atR (aview SEGS (w_H W) mem2) p l).
{ intros p l Hp Hpl Hb. eapply (abytes_atR_kept _ _ lo hi); [exact HK | exact Hb | lia | lia | lia]. }
assert (LT : (length RO_g_instance_verbs = 144)%nat) by (vm_compute; reflexivity).
assert (LS1 : (length RO_lit_224c0 = 3)%nat) by (vm_compute; reflexivity).
assert (LS2 : (length RO_lit_22d80 = 2)%nat) by (vm_compute; reflexivity).
assert (LL : forall j, (j < 18)%nat -> (length (nth j iiv_lits []) <= 100)%nat).
{ intros j Hj. do 18 (destruct j as [|j]; [vm_compute; lia|]). cbn in Hj. lia. }
split; [apply HBY; [unfold A_TAB; lia | rewrite LT; unfold A_TAB; lia | exact HT]|].
split; [apply HBY; [unfold A_SEPS; lia | rewrite LS1; unfold A_SEPS; lia | exact HS1]|].
split; [apply HBY; [unfold A_SP; lia | rewrite LS2; unfold A_SP; lia | exact HS2]|].
split.
{ intros j Hj. destruct (iiv_addr_range j Hj) as [Ha1 Ha2]. pose proof (LL j Hj) as HLj.
  apply HBY; [lia | lia | exact (HL j Hj)]. }
split.
{ intros j Hj. pose proof (iiv_ends_low _ (iiv_tail_in j Hj)) as He. apply HTV; [exact He | exact (HTl j Hj)]. }
split.
- apply HTV; [unfold A_SEPS; lia | exact HE1].
- apply HTV; [unfold A_SP; lia | exact HE2].
Qed.

Lemma iiv_frame_kept : forall (W : world SEGS) mem1 mem2 sp0 (regs0 : bvmap 5 word) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) ->
hi <= sp0 - 80 -> 80 <= sp0 -> sp0 < 2 ^ 64 ->
iiv_frame (mrestrict (w_H W) mem1) sp0 regs0 -> iiv_frame (mrestrict (w_H W) mem2) sp0 regs0.
Proof.
intros W mem1 mem2 sp0 regs0 lo hi HK Hhi Hsp0 Hsp64 HFR j r Hj k Hk.
assert (Hj9 : (j < 9)%nat) by (do 9 (destruct j as [|j]; [lia|]); unfold iiv_saved in Hj; destruct j; cbn in Hj; discriminate Hj).
assert (Ha : 0 <= sp0 - 8 - 8 * Z.of_nat j + Z.of_nat k < 2 ^ 64) by lia.
assert (Hna : ~ (lo <= sp0 - 8 - 8 * Z.of_nat j + Z.of_nat k < hi)) by lia.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem1 mem2 _ (HK _ Ha Hna)).
exact (HFR j r Hj k Hk).
Qed.

(* the memory facts of iiv_memF other than the caller's frame *)
Definition iiv_memP (W : world SEGS) (mem1 : word -> option byte) (sp0 t : Z) (tb : list byte) : Prop :=
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem1) /\
iiv_roF W mem1 /\
aguard_ok SEGS W mem1 0xa7098 0x6045d8 /\
astr_atR (aview SEGS (w_H W) mem1) t tb /\
t + Z.of_nat (length tb) + 1 <= alloc_ceiling /\
(forall rq, spZ rq = sp0 - 80 -> aread_ok SEGS (2 * ESTACK) W rq mem1 t (Z.of_nat (length tb) + 1)) /\
atail_vis SEGS W mem1 (t + Z.of_nat (length tb)).

(* they survive any write inside [lo, hi) when lo lies between the heap and the wrappers' window *)
Lemma iiv_memP_win : forall (W : world SEGS) mem1 mem2 sp0 t tb lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) ->
alloc_ceiling <= lo -> lo <= sp0 - 80 - 2 * ESTACK -> sp0 <= 2 ^ 47 -> 0 < t ->
iiv_memP W mem1 sp0 t tb -> iiv_memP W mem2 sp0 t tb.
Proof.
intros W mem1 mem2 sp0 t tb lo hi HK Hlo Hlo2 Hsp47 Ht0 (HROM & HROF & HG & HSTR & Htc & HRD & HTL).
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
assert (ESTACK = 4096) as Hes by reflexivity.
assert (KO : kept_out (aview SEGS (w_H W) mem1) (aview SEGS (w_H W) mem2) lo hi)
by (intros a Ha Hna; exact (HK a Ha Hna)).
split.
{ intros a Hro Ho He. pose proof (iiv_ro_img a Hro) as Ha.
  rewrite (HK a ltac:(lia) ltac:(lia)). exact (HROM a Hro Ho He). }
split; [eapply iiv_roF_kept; [exact KO | lia | lia | exact HROF]|].
split; [eapply (aguard_ok_kept SEGS W mem1 mem2 _ _ _ _ KO HG); lia|].
split; [eapply (astr_atR_kept _ _ _ _ _ _ KO HSTR); lia|].
split; [exact Htc|].
split.
{ intros rq Hrq. eapply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W rq rq mem1 mem2 _ _ _ _ KO (HRD rq Hrq));
  unfold kHighShadowEnd in *; lia. }
assert (He : 0 <= t + Z.of_nat (length tb) < alloc_ceiling) by lia.
pose proof (tail_below _ _ He CR4) as Htb.
eapply (atail_vis_kept SEGS W mem1 mem2 _ _ _ KO HTL); lia.
Qed.

Lemma iiv_memF_of : forall (W : world SEGS) mem1 sp0 t tb (regs0 : bvmap 5 word),
iiv_memP W mem1 sp0 t tb -> iiv_frame (mrestrict (w_H W) mem1) sp0 regs0 -> iiv_memF W mem1 sp0 t tb regs0.
Proof.
intros W mem1 sp0 t tb regs0 (H1 & H2 & H3 & H4 & H5 & H6 & H7) HF.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7 | exact HF].
Qed.

Lemma iiv_memF_kept : forall (W : world SEGS) mem1 mem2 sp0 t tb (regs0 : bvmap 5 word),
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
 aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) ->
alloc_ceiling + 80 + 2 * ESTACK <= sp0 -> sp0 <= 2 ^ 47 -> 0 < t ->
iiv_memF W mem1 sp0 t tb regs0 -> iiv_memF W mem2 sp0 t tb regs0.
Proof.
intros W mem1 mem2 sp0 t tb regs0 HK Hsp Hsp47 Ht0 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & HFR).
assert (ESTACK = 4096) as Hes by reflexivity.
apply iiv_memF_of.
- apply (iiv_memP_win W mem1 mem2 sp0 t tb (sp0 - 80 - 2 * ESTACK) (sp0 - 80) HK ltac:(lia) ltac:(lia) Hsp47 Ht0).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact H5|]. split; [exact H6 | exact H7].
- exact (iiv_frame_kept W mem1 mem2 sp0 regs0 _ _ HK ltac:(lia) ltac:(lia) ltac:(lia) HFR).
Qed.

(* the facts every lemma below takes from the invariant at a state seeded from iiv_extra *)
Ltac iiv_env HE E regs regs0 EE EX :=
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r);
[ intros m r Hm; rewrite HE; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm |];
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = getr regs0 (Z_to_bv 5 (nth j iiv_saved 0)));
[ intros j Hj; rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite ew_Ereg_extra; apply iiv_extra_old; exact Hj |].

Ltac iiv_unchanged UN HFr :=
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN.

Ltac iiv_sv Ss EX k :=
let Sk := fresh "Sk" in let Xk := fresh "Xk" in
pose proof (Ss k ltac:(lia)) as Sk; pose proof (EX k ltac:(lia)) as Xk;
cbn [nth iiv_saved Nat.add] in Sk, Xk; rewrite Sk; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Xk.

(* the epilogue's registers: sp back to sp0, s0..s7 and ra from the frame, gp/tp/s8..s11 untouched *)
Lemma iiv_ret_ok : forall E ss (ms : machine_state) (H : word -> bool) (regs regs0 : bvmap 5 word) sp0,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
sr_get (ss_regs ss) 1 = SOff 32 0 -> sr_get (ss_regs ss) 2 = SOff 2 80 ->
sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
(forall j, (1 <= j < 9)%nat -> sr_get (ss_regs ss) (Z_to_bv 5 (nth j iiv_saved 0)) = SOff (32 + j) 0) ->
(forall r, 24 <= r <= 27 -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
(forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r) ->
(forall j, (j < 9)%nat -> ew E (32 + j) = getr regs0 (Z_to_bv 5 (nth j iiv_saved 0))) ->
spZ regs = sp0 - 80 -> getr regs0 2 = w64 sp0 ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
(forall r, 24 <= r <= 27 -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
getr (ms_regs ms) 1 = getr regs0 1 /\ aregs_preserved regs0 (ms_regs ms).
Proof.
intros E ss ms H regs regs0 sp0 HS S1 S2 S3 S4 Ss Sh EE EX Hsp H2 H3 H4 Hhi.
assert (RG : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. exact (st_ok_pi_restrict_reg H E ss ms r HS). }
split.
{ rewrite RG, S1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 0%nat ltac:(lia)). }
apply iiv_aregs.
- rewrite RG, S2. cbn [sv_denot]. rewrite (EE 2%nat 2%bv eq_refl). unfold spZ in Hsp. rewrite Hsp, H2.
  unfold w64. f_equal. lia.
- rewrite RG, S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl). exact H3.
- rewrite RG, S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl). exact H4.
- intros r Hr. rewrite RG.
  assert (Hc : r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ 24 <= r <= 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | Hc]]]]]]]];
  [ iiv_sv Ss EX 1%nat | iiv_sv Ss EX 2%nat | iiv_sv Ss EX 3%nat | iiv_sv Ss EX 4%nat
  | iiv_sv Ss EX 5%nat | iiv_sv Ss EX 6%nat | iiv_sv Ss EX 7%nat | iiv_sv Ss EX 8%nat
  | rewrite (Sh r Hc); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32;
      rewrite Z.mod_small by lia; lia);
    exact (Hhi r Hc) ].
Qed.

(* from the step block of pass n, which found no match: the back edge goes to the header of pass n + 1, or after
   pass 17 the function returns 0 *)
Lemma iiv_tail : forall ly S (W : world SEGS) mem md sp0 t tb (regs0 : bvmap 5 word) n regs mem1 md1,
iiv_fixed regs0 sp0 t tb ->
iiv_inv ly S W mem md sp0 t tb regs0 n regs mem1 md1 ->
existsb (verb_is_m tb) (firstn (Z.to_nat (n + 1)) Lit.instance_verb_formats) = false ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + IIV_STEP)) mem1 (seg_rom SEGS)) md1)
(fun W' c' => iiv_post ly S W mem md sp0 tb regs0 W' c'
\/ (W' = W /\ exists regs' mem' md', c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + IIV_LOOP)) mem' (seg_rom SEGS)) md'
/\ n < 17 /\ iiv_inv ly S W mem md sp0 t tb regs0 (n + 1) regs' mem' md')).
Proof.
intros ly S W mem md sp0 t tb regs0 n regs mem1 md1 FX INV HFX1.
pose proof FX as (VOBJS & HNZ & Ht0 & Hlen32 & Hraw0 & Hsp0r & Hgp0 & Htp0 & AMt).
destruct INV as (Hn & HJ & HM & Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H21 & H22 & H23 & Hhi & HFX).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & HFR).
destruct (iiv_seed_step W regs regs0 mem1 ly S md1 sp0 n HAR Hstk HFR Hsp) as [HS SHOK].
remember (Eimg (Ereg regs (iiv_extra regs0 n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
iiv_env HE E regs regs0 EE EX. clear HE.
assert (E20 : ew E 20 = Z_to_bv 64 (- (8 * n))) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E23 : ew E 23 = Z_to_bv 64 (-144)) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
paj_run_tok RUN HS HJ SHOK iiv_Bspan.
{ iiv_awr. }
iiv_unchanged UN1 HFr. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK iiv_Bspan.
- rewrite branch_ne_U, (iiv_U _ 20 (-8) _ E20), (iiv_U _ 23 0 _ E23), (iiv_back n Hn) in Hc.
  assert (Hn17 : n < 17) by (destruct (Z.eqb_spec n 17); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK iiv_Bspan IIV_LOOP.
  { iiv_awr. }
  iiv_unchanged UN2 HFr. clear HF HFr HG.
  pmkst HS.
  apply SRr_ret. right. split; [reflexivity|].
  eexists _, _, _. split; [reflexivity|]. split; [exact Hn17|].
  split; [lia|]. split; [exact HJ|]. split.
  { eapply iiv_memF_kept; [| lia | lia | exact Ht0 | exact HM].
    intros a Ha _. rewrite (UN2 a Ha (fun x => x)), (UN1 a Ha (fun x => x)). reflexivity. }
  split; [unfold spZ; iiv_sreg HS; rewrite (EE 2%nat 2%bv eq_refl); exact Hsp|].
  split; [iiv_sreg HS; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp|].
  split; [iiv_sreg HS; rewrite (EE 4%nat 4%bv eq_refl); exact Htp|].
  split; [iiv_sreg HS; rewrite (EE 8%nat 8%bv eq_refl); exact H8|].
  split; [iiv_sreg HS; rewrite (EE 9%nat 9%bv eq_refl); exact H9|].
  split; [iiv_sreg HS; rewrite (EE 18%nat 18%bv eq_refl); exact H18|].
  split; [iiv_sreg HS; rewrite E20, iiv_wrap_add; unfold w64; f_equal; lia|].
  split; [iiv_sreg HS; rewrite (EE 21%nat 21%bv eq_refl), H21; unfold w64; rewrite iiv_wrap_add; f_equal; lia|].
  split; [iiv_sreg HS; rewrite (EE 22%nat 22%bv eq_refl), H22; unfold w64; rewrite iiv_wrap_add; f_equal; lia|].
  split; [iiv_sreg HS; rewrite (EE 23%nat 23%bv eq_refl); exact H23|].
  split; [|exact HFX1].
  intros r Hr.
  assert (Hc4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc4 as [-> | [-> | [-> | ->]]]; iiv_sreg HS;
  [ rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl) | rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl)
  | rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl) | rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl) ]; apply Hhi; lia.
- rewrite branch_ne_U, (iiv_U _ 20 (-8) _ E20), (iiv_U _ 23 0 _ E23), (iiv_back n Hn) in Hc.
  assert (Hn17 : n = 17) by (destruct (Z.eqb_spec n 17); [lia | discriminate]).
  paj_run_tok RUN HS HJ SHOK iiv_Bspan.
  { iiv_awr. }
  iiv_unchanged UN2 HFr. clear HF HFr HG.
  destruct (iiv_ret_ok E _ _ _ regs regs0 sp0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(intros j Hj; do 9 (destruct j as [|j]; [first [lia | vm_compute; reflexivity]|]); lia)
    ltac:(intros r Hr; assert (Hc4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
          destruct Hc4 as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity)
    EE EX Hsp Hsp0r ltac:(rewrite Hgp, Hgp0; reflexivity) ltac:(rewrite Htp, Htp0; reflexivity) Hhi) as [Rra Rpres].
  prreg HS (10%bv : bv 5) Ra0.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. left. unfold iiv_post.
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
  split; [rewrite Rra; unfold YK0s.ret_ok in Hraw0; rewrite Hraw0; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split; [exact Rpres|].
  rewrite Ra0. subst n. rewrite (iiv_none tb HFX1). reflexivity.
Qed.

(* an image range a wrapper reads: its bytes, its shadow (the record) and its place below the stack *)
Lemma iiv_aread_img : forall ly S (W : world SEGS) mem md (rq : bvmap 5 word) a k l,
AR SEGS B ly S W mem md -> In (a, k) iiv_ro_ranges -> k = Z.of_nat (length l) ->
abytes_atR (aview SEGS (w_H W) mem) a l -> 0 <= a -> a + k <= 0x606000 ->
alloc_ceiling <= spZ rq - 2 * ESTACK -> 0 < k ->
aread_ok SEGS (2 * ESTACK) W rq mem a k.
Proof.
intros ly S W mem md rq a k l HAR Hin Hk Hb Ha0 Ha1 Hsp Hk0.
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
destruct (iiv_img_ok ly S W mem md a k HAR Hin) as [HRA HHV].
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros x Hx. split.
  - replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite (Hb (Z.to_nat (x - a)) ltac:(lia)). discriminate.
  - unfold ascratch_stk. lia. }
split; [unfold amem_range, kLowMemEnd; lia|].
split; [exact HRA | intros _; exact HHV].
Qed.

Lemma iiv_aread_prefix : forall stk (W : world SEGS) (rq : bvmap 5 word) mem x n m,
aread_ok SEGS stk W rq mem x n -> 0 <= m <= n -> aread_ok SEGS stk W rq mem x m.
Proof.
intros stk W rq mem x n m (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hm.
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|].
split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hm0 s Hs. apply (H6 ltac:(lia) s).
assert (Q1 : (x + m - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Q2 : shadow_addr (x + m - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; lia).
assert (Q3 : shadow_addr (x + m - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma iiv_region_kept : forall E (W : world SEGS) m m2 nn b lo hi cs klo khi,
bv_unsigned (ew E nn) = b ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (klo <= a < khi) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
(b + hi <= klo \/ khi <= b + lo) -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m2) (YP09.mkRegion (Some nn) lo hi 0 0 cs).
Proof.
intros E W m m2 nn b lo hi cs klo khi Hb HK Hd H0 H1.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hb.
- intros a Ha. apply (mbyte_of_aview SEGS). apply HK; lia.
- intros a Ha. lia.
Qed.

(* a state of pass n after a call or a run: memory kept outside the call window, the callee-saved registers the
   invariant names kept *)
Lemma iiv_inv_move : forall ly S (W : world SEGS) mem md sp0 t tb (regs0 : bvmap 5 word) n regs mem1 md1
(regs' : bvmap 5 word) mem' md',
0 < t ->
iiv_inv ly S W mem md sp0 t tb regs0 n regs mem1 md1 ->
ajournal SEGS B IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W mem' md' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
 aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem1 a) ->
(forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ 20 <= r <= 27 ->
 getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
iiv_inv ly S W mem md sp0 t tb regs0 n regs' mem' md'.
Proof.
intros ly S W mem md sp0 t tb regs0 n regs mem1 md1 regs' mem' md' Ht0
(Hn & HJ & HM & Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H21 & H22 & H23 & Hhi & HFX) HJ' HK HR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
split; [exact Hn|]. split; [exact HJ'|]. split; [eapply iiv_memF_kept; [exact HK | lia | lia | exact Ht0 | exact HM]|].
split; [unfold spZ in *; rewrite <- Hsp; f_equal; exact (HR 2 ltac:(lia))|].
split; [rewrite <- Hgp; exact (HR 3 ltac:(lia))|]. split; [rewrite <- Htp; exact (HR 4 ltac:(lia))|].
split; [rewrite <- H8; exact (HR 8 ltac:(lia))|]. split; [rewrite <- H9; exact (HR 9 ltac:(lia))|].
split; [rewrite <- H18; exact (HR 18 ltac:(lia))|]. split; [rewrite <- H20; exact (HR 20 ltac:(lia))|].
split; [rewrite <- H21; exact (HR 21 ltac:(lia))|]. split; [rewrite <- H22; exact (HR 22 ltac:(lia))|].
split; [rewrite <- H23; exact (HR 23 ltac:(lia))|].
split; [intros r Hr; rewrite (HR r ltac:(lia)); exact (Hhi r Hr) | exact HFX].
Qed.

Ltac iiv_regs_kept HS EE oldtac :=
let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
intros r Hr;
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
 r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
iiv_sreg HS; oldtac; apply EE; reflexivity.

(* the image ranges and the separator string a pass hands its two wrappers *)
Lemma iiv_fmt_str : forall (W : world SEGS) mem n, (n < 18)%nat -> iiv_roF W mem ->
astr_at SEGS W mem (iiv_addr n) (iiv_fmt n).
Proof.
intros W mem n Hn (_ & _ & _ & HL & _). split; [|exact (iiv_fmt_nz n Hn)].
apply (proj1 (abytes_atR_view SEGS W mem _ _)). rewrite <- (iiv_lit_fmt n Hn). exact (HL n Hn).
Qed.

Lemma iiv_sp_str : forall (W : world SEGS) mem, iiv_roF W mem -> astr_at SEGS W mem A_SP iiv_spl.
Proof.
intros W mem (_ & _ & HS2 & _). split.
- apply (proj1 (abytes_atR_view SEGS W mem _ _)). exact HS2.
- intros [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H | exact H].
Qed.

Lemma iiv_seps_str : forall (W : world SEGS) mem, iiv_roF W mem -> astr_at SEGS W mem A_SEPS iiv_seps.
Proof.
intros W mem (_ & HS1 & _). split.
- apply (proj1 (abytes_atR_view SEGS W mem _ _)). exact HS1.
- intros [H|[H|H]]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H
  | apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H | exact H].
Qed.

Lemma iiv_fmt_read : forall ly S (W : world SEGS) mem md (rq : bvmap 5 word) n,
AR SEGS B ly S W mem md -> (n < 18)%nat -> iiv_roF W mem -> alloc_ceiling <= spZ rq - 2 * ESTACK ->
aread_ok SEGS (2 * ESTACK) W rq mem (iiv_addr n) (astr_len (iiv_fmt n) + 1).
Proof.
intros ly S W mem md rq n HAR Hn (_ & _ & _ & HL & _) Hsp.
destruct (iiv_addr_range n Hn) as [Ha1 Ha2].
assert (LL : (length (nth n iiv_lits []) <= 100)%nat).
{ do 18 (destruct n as [|n]; [vm_compute; lia|]). cbn in Hn. lia. }
pose proof (iiv_lit_len n Hn) as HLn. unfold astr_len.
eapply (iiv_aread_img ly S W mem md rq _ _ (nth n iiv_lits [])); [exact HAR | exact (iiv_range_in n Hn)
| exact HLn | exact (HL n Hn) | lia | lia | exact Hsp | lia].
Qed.

(* pass n from the loop header: strcspn(f_n, " "), the length test, strncmp(t, f_n, |tfirst t|), and either the
   return of 1 or the step block of pass n *)
Lemma iiv_body : forall ly S (W : world SEGS) mem md sp0 t tb (regs0 : bvmap 5 word) n regs mem1 md1,
iiv_fixed regs0 sp0 t tb ->
iiv_inv ly S W mem md sp0 t tb regs0 n regs mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + IIV_LOOP)) mem1 (seg_rom SEGS)) md1)
(fun W' c' => iiv_post ly S W mem md sp0 tb regs0 W' c'
\/ (W' = W /\ exists regs' mem' md', c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + IIV_LOOP)) mem' (seg_rom SEGS)) md'
/\ n < 17 /\ iiv_inv ly S W mem md sp0 t tb regs0 (n + 1) regs' mem' md')).
Proof.
intros ly S W mem md sp0 t tb regs0 n regs mem1 md1 FX INV.
pose proof FX as (VOBJS & HNZ & Ht0 & Hlen32 & Hraw0 & Hsp0r & Hgp0 & Htp0 & AMt).
pose proof INV as (Hn & HJ & HM & Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H21 & H22 & H23 & Hhi & HFX).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof HM as (HROD & HROF & HG & HSTR & Htc & HRDt & HTLt & HFR).
pose proof HROF as (HT & _ & _ & _ & _ & _ & _).
remember (Z.to_nat n) as nn eqn:Hnn0.
assert (Hnn : (nn < 18)%nat) by lia. assert (Enn : n = Z.of_nat nn) by lia.
destruct (iiv_seed_loop W regs regs0 mem1 ly S md1 sp0 n HAR Hstk ltac:(lia) HT HFR Hsp H21 H22) as [HS SHOK].
remember (Eimg (Ereg regs (iiv_extra regs0 n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
iiv_env HE E regs regs0 EE EX.
assert (E41 : ew E 41 = Z_to_bv 64 (iiv_addr nn)).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). change 41%nat with (32 + 9)%nat. rewrite ew_Ereg_extra.
  rewrite iiv_extra_fmt. rewrite Hnn0. reflexivity. }
clear HE.
assert (U2 : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (U21 : bv_unsigned (ew E 21) = A_TAB + 8 * n).
{ rewrite (EE 21%nat 21%bv eq_refl), H21. unfold w64. apply unsigned_lit_small. unfold A_TAB. lia. }
assert (U22 : bv_unsigned (ew E 22) = A_SHB + n).
{ rewrite (EE 22%nat 22%bv eq_refl), H22. unfold w64. apply unsigned_lit_small. unfold A_SHB. lia. }
destruct (iiv_addr_range nn Hnn) as [Ha1 Ha2].
assert (Hlt : (length (tfirst tb) <= length tb)%nat) by apply upto_length.
assert (Hlf : (length (vfirst (iiv_fmt nn)) <= length (iiv_fmt nn))%nat) by apply upto_length.
assert (LL : (length (iiv_fmt nn) <= 100)%nat).
{ pose proof (iiv_lit_len nn Hnn) as HLn. clear - Hnn HLn.
  assert (L2 : (length (nth nn iiv_lits []) <= 101)%nat).
  { do 18 (destruct nn as [|nn]; [vm_compute; lia|]). cbn in Hnn. lia. }
  lia. }
(* the header, the inline check and the table load, up to strcspn(f_n, " ") *)
paj_run_tok RUN HS HJ SHOK iiv_Bspan.
{ iiv_awr. }
iiv_unchanged UN1 HFr. clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (HM1 : iiv_memF W (ms_mem ms) sp0 t tb regs0).
{ eapply iiv_memF_kept; [| lia | lia | exact Ht0 | exact HM]. intros a Ha _. exact (UN1 a Ha (fun x => x)). }
pose proof HM1 as (HROD1 & HROF1 & HG1 & HSTR1 & _ & _ & _ & _).
pose proof (proj1 HJ) as HAR1.
assert (Hsp1 : spZ (ms_regs ms) = sp0 + -80) by (unfold spZ; rewrite Q2, U2; lia).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcspn) W (ms_regs ms) (ms_mem ms) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md []
  ly S _ 0 (-80) _ _ HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Q1 ltac:(intros a [])).
  apply (STRCSPN fx ly S W (ms_regs ms) (ms_mem ms) _ (iiv_addr nn) A_SP (iiv_fmt nn) iiv_spl).
  - exact HG1.
  - apply (ecall_pre_stk_at SEGS B (2 * ESTACK) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms) _ 0
    (ms_regs ms) (-80) HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    + rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    + rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Q10, E41. reflexivity.
  - rewrite Q11, (EE 18%nat 18%bv eq_refl). exact H18.
  - lia.
  - unfold A_SP. lia.
  - exact (iiv_fmt_str W _ nn Hnn HROF1).
  - exact (iiv_sp_str W _ HROF1).
  - exact (iiv_fmt_read ly S W _ _ (ms_regs ms) nn HAR1 Hnn HROF1 ltac:(lia)).
  - apply PaLibH.amem8_of_low; unfold astr_len, kLowMemEnd; lia.
  - pose proof HROF1 as (_ & _ & HS21 & _).
    eapply (iiv_aread_img ly S W _ _ (ms_regs ms) A_SP _ RO_lit_22d80 HAR1 iiv_sp_in); [reflexivity | exact HS21
    | unfold A_SP; lia | unfold A_SP; lia | lia | lia].
  - change (astr_len iiv_spl) with 1. apply PaLibH.amem8_of_low; unfold A_SP, kLowMemEnd; lia.
  - pose proof HROF1 as (_ & _ & _ & _ & HTl1 & _). exact (HTl1 nn Hnn).
  - pose proof HROF1 as (_ & _ & _ & _ & _ & _ & HE21). exact HE21.
  - exact (iiv_romv W _ HROD1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & Hkeep).
assert (KEPT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hna. apply Hkeep; [exact Ha | lia | exact (fun H => H)]. }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
specialize (HS2 ltac:(repeat apply Forall_cons; try apply Forall_nil;
  [ eapply (iiv_region_kept E W _ _ 2 (sp0 - 80)); [exact U2 | exact KEPT2 | lia | lia | lia]
  | eapply (iiv_region_kept E W _ _ 21 (A_TAB + 8 * n)); [exact U21 | exact KEPT2 | unfold A_TAB; lia | unfold A_TAB; lia | unfold A_TAB; lia]
  | eapply (iiv_region_kept E W _ _ 22 (A_SHB + n)); [exact U22 | exact KEPT2 | unfold A_SHB; lia | unfold A_SHB; lia | unfold A_SHB; lia] ])).
clear HS HJ SHOK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename HJ2 into HJ.
remember (havoc E 48 _) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD2 : forall m, (m < 48)%nat -> ew E2 m = ew E m) by (intros m Hm; rewrite HE2, ew_havoc_old by lia; reflexivity).
clear HE2.
assert (SHOK : sh_ok SEGS iiv_Bx iiv_SH E2 (mrestrict (w_H W) mem2)) by constructor.
prreg HS (10%bv : bv 5) R10.
(* the length test *)
paj_run_tok RUN HS HJ SHOK iiv_Bspan.
{ iiv_awr. }
iiv_unchanged UN2 HFr. clear HF HFr HG.
assert (Ur9 : U E2 (SOff 9 0) = Z.of_nat (length (tfirst tb))).
{ rewrite (iiv_U E2 9 0 (Z.of_nat (length (tfirst tb)))); [rewrite Z.add_0_r; apply Z.mod_small; lia|].
  rewrite OLD2 by lia. rewrite (EE 9%nat 9%bv eq_refl). exact H9. }
assert (Ur52 : U E2 (SOff 52 0) = Z.of_nat (length (vfirst (iiv_fmt nn)))).
{ rewrite (iiv_U E2 52 0 (Z.of_nat (cspn_len iiv_spl (iiv_fmt nn)))).
  - rewrite Z.add_0_r, iiv_cspn_f. apply Z.mod_small. lia.
  - cbn [ms_regs restrict mkst] in R10. rewrite <- R10. exact HQ2. }
psrr_branch_tok RUN BR HS SHOK iiv_Bspan.
- (* the lengths differ: no match, to the step block *)
  rewrite branch_ne_U, Ur9, Ur52 in Hc.
  assert (Hne : length (tfirst tb) <> length (vfirst (iiv_fmt nn))) by (destruct (Z.eqb_spec (Z.of_nat (length (tfirst tb))) (Z.of_nat (length (vfirst (iiv_fmt nn))))); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK iiv_Bspan IIV_STEP.
  { iiv_awr. }
  iiv_unchanged UN3 HFr. clear HF HFr HG.
  pmkst HS.
  apply (iiv_tail ly S W mem md sp0 t tb regs0 n _ _ _ FX).
  + eapply (iiv_inv_move ly S W mem md sp0 t tb regs0 n regs mem1 md1); [exact Ht0 | exact INV | exact HJ | |].
    * intros a Ha Hna. rewrite (UN3 a Ha (fun x => x)), (UN2 a Ha (fun x => x)), (KEPT2 a Ha Hna).
      exact (UN1 a Ha (fun x => x)).
    * iiv_regs_kept HS EE ltac:(rewrite OLD2 by lia).
  + replace (Z.to_nat (n + 1)) with (Datatypes.S nn) by lia.
    apply iiv_firstn_S; [exact Hnn | exact HFX | apply iiv_step_ne; [exact Hnn | exact Hne]].
- (* the lengths agree: strncmp(t, f_n, |tfirst t|) *)
  rewrite branch_ne_U, Ur9, Ur52 in Hc.
  assert (Heq : length (tfirst tb) = length (vfirst (iiv_fmt nn))) by (destruct (Z.eqb_spec (Z.of_nat (length (tfirst tb))) (Z.of_nat (length (vfirst (iiv_fmt nn))))); [lia | discriminate]).
  clear Hc. paj_run_tok RUN HS HJ SHOK iiv_Bspan.
  { iiv_awr. }
  iiv_unchanged UN3 HFr. clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  assert (KEPT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem1 a).
  { intros a Ha Hna. rewrite (UN3 a Ha (fun x => x)), (UN2 a Ha (fun x => x)), (KEPT2 a Ha Hna).
    exact (UN1 a Ha (fun x => x)). }
  assert (HM3 : iiv_memF W (ms_mem ms1) sp0 t tb regs0) by (eapply iiv_memF_kept; [exact KEPT3 | lia | lia | exact Ht0 | exact HM]).
  pose proof HM3 as (HROD3 & HROF3 & HG3 & HSTR3 & Htc3 & HRDt3 & HTLt3 & _).
  pose proof (proj1 HJ) as HAR3.
  assert (Hsp3 : spZ (ms_regs ms1) = sp0 + -80) by (unfold spZ; rewrite P2, OLD2, U2 by lia; lia).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIGMA CS___interceptor_trampoline_strncmp) W (ms_regs ms1) (ms_mem ms1) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md []
    ly S _ 0 (-80) _ _ HJ Hsp3 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) P1 ltac:(intros a [])).
    apply (STRNCMP fx ly S W (ms_regs ms1) (ms_mem ms1) _ t (iiv_addr nn) (Z.of_nat (length (tfirst tb))) tb (iiv_fmt nn)).
    - apply (ecall_pre_stk_at SEGS B (2 * ESTACK) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms1) _ 0
      (ms_regs ms1) (-80) HJ Hsp3 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)).
      + rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
      + rewrite P3, OLD2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
      + rewrite P4, OLD2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
    - rewrite P10, OLD2, (EE 8%nat 8%bv eq_refl) by lia. exact H8.
    - rewrite P11, OLD2, E41 by lia. reflexivity.
    - rewrite P12, OLD2, (EE 9%nat 9%bv eq_refl) by lia. exact H9.
    - lia.
    - lia.
    - lia.
    - apply (proj1 (astr_atR_view SEGS W _ _ _)). exact HSTR3.
    - exact (iiv_fmt_str W _ nn Hnn HROF3).
    - apply (iiv_aread_prefix _ W _ _ _ (Z.of_nat (length tb) + 1)); [apply HRDt3; lia | unfold astr_len; lia].
    - exact AMt.
    - apply (iiv_aread_prefix _ W _ _ _ (astr_len (iiv_fmt nn) + 1));
      [exact (iiv_fmt_read ly S W _ _ (ms_regs ms1) nn HAR3 Hnn HROF3 ltac:(lia)) | unfold astr_len; lia].
    - apply PaLibH.amem8_of_low; unfold astr_len, kLowMemEnd; lia.
    - exact HTLt3.
    - pose proof HROF3 as (_ & _ & _ & _ & HTl3 & _). exact (HTl3 nn Hnn).
    - exact (iiv_romv W _ HROD3). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HQ4 & Hkeep4).
  assert (KEPT4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem ms1) a).
  { intros a Ha Hna. apply Hkeep4; [exact Ha | lia | exact (fun H => H)]. }
  assert (U2' : bv_unsigned (ew E2 2) = sp0 - 80) by (rewrite OLD2 by lia; exact U2).
  assert (U21' : bv_unsigned (ew E2 21) = A_TAB + 8 * n) by (rewrite OLD2 by lia; exact U21).
  assert (U22' : bv_unsigned (ew E2 22) = A_SHB + n) by (rewrite OLD2 by lia; exact U22).
  jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2]%nat HS4.
  specialize (HS4 ltac:(repeat apply Forall_cons; try apply Forall_nil;
    [ eapply (iiv_region_kept E2 W _ _ 2 (sp0 - 80)); [exact U2' | exact KEPT4 | lia | lia | lia]
    | eapply (iiv_region_kept E2 W _ _ 21 (A_TAB + 8 * n)); [exact U21' | exact KEPT4 | unfold A_TAB; lia | unfold A_TAB; lia | unfold A_TAB; lia]
    | eapply (iiv_region_kept E2 W _ _ 22 (A_SHB + n)); [exact U22' | exact KEPT4 | unfold A_SHB; lia | unfold A_SHB; lia | unfold A_SHB; lia] ])).
  clear HS HJ SHOK. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS. rename HJ4 into HJ.
  remember (havoc E2 64 _) as E4 eqn:HE4 in HS.
  assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [assumption | cbv; lia]).
  assert (OLD4 : forall m, (m < 64)%nat -> ew E4 m = ew E2 m) by (intros m Hm; rewrite HE4, ew_havoc_old by lia; reflexivity).
  clear HE4.
  assert (SHOK : sh_ok SEGS iiv_Bx iiv_SH E4 (mrestrict (w_H W) mem4)) by constructor.
  prreg HS (10%bv : bv 5) S10.
  destruct (iiv_step_eq tb nn Hnn HNZ Heq) as (v & Hv & Rv & Qv).
  rewrite (iiv_lit_fmt nn Hnn) in Hv.
  (* beqz a0 *)
  paj_run_tok RUN HS HJ SHOK iiv_Bspan.
  { iiv_awr. }
  iiv_unchanged UN4 HFr. clear HF HFr HG.
  assert (Ua0 : U E4 (SOff 68 0) = bv_unsigned (getr regs4 10)).
  { rewrite U_SOff. cbn [ms_regs restrict mkst] in S10. rewrite <- S10, Z.add_0_r. unfold zcanon, M64.
    apply Z.mod_small. apply bv_unsigned_in_range. }
  psrr_branch_tok RUN BR HS SHOK iiv_Bspan.
  + (* a0 = 0: the token names format n, return 1 *)
    rewrite branch_eq_U, Ua0 in Hc. replace (U E4 (SLit 0)) with 0 in Hc by reflexivity.
    apply Z.eqb_eq in Hc.
    assert (Hz : getr regs4 10 = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
    assert (Hm : verb_is_m tb (iiv_fmt nn) = true).
    { rewrite <- Qv. apply Z.eqb_eq. apply (proj1 HQ4) in Hz. rewrite Hv in Hz. injection Hz as Hz. exact Hz. }
    paj_run_tok RUN HS HJ SHOK iiv_Bspan.
    { iiv_awr. }
    iiv_unchanged UN5 HFr. clear HF HFr HG.
    assert (EE4 : forall m (r : bv 5), (m < 48)%nat -> Z.of_nat m = bv_unsigned r -> ew E4 m = getr regs r).
    { intros m r Hm0 Hm1. rewrite OLD4, OLD2 by lia. exact (EE m r Hm1). }
    assert (EX4 : forall j, (j < 9)%nat -> ew E4 (32 + j) = getr regs0 (Z_to_bv 5 (nth j iiv_saved 0))).
    { intros j Hj. rewrite OLD4, OLD2 by lia. exact (EX j Hj). }
    destruct (iiv_ret_ok E4 _ _ _ regs regs0 sp0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(intros j Hj; do 9 (destruct j as [|j]; [first [lia | vm_compute; reflexivity]|]); lia)
      ltac:(intros r Hr; assert (Hc4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
            destruct Hc4 as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity)
      ltac:(intros m r Hmr; destruct (Nat.lt_ge_cases m 48) as [Hl | Hl]; [exact (EE4 m r Hl Hmr) |
            pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; lia])
      EX4 Hsp Hsp0r ltac:(rewrite Hgp, Hgp0; reflexivity) ltac:(rewrite Htp, Htp0; reflexivity) Hhi) as [Rra Rpres].
    prreg HS (10%bv : bv 5) Ra0.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. left. unfold iiv_post.
    lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists rg, m, d end.
    split; [rewrite Rra; unfold YK0s.ret_ok in Hraw0; rewrite Hraw0; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
    split; [exact Rpres|].
    rewrite Ra0, (iiv_found tb nn Hnn Hm). reflexivity.
  + (* a0 <> 0: no match, to the step block *)
    rewrite branch_eq_U, Ua0 in Hc. replace (U E4 (SLit 0)) with 0 in Hc by reflexivity.
    apply Z.eqb_neq in Hc.
    assert (Hm : verb_is_m tb (iiv_fmt nn) = false).
    { rewrite <- Qv. apply Z.eqb_neq. intros Hv0. subst v. apply Hc.
      assert (Hz : getr regs4 10 = w64 0) by (apply (proj2 HQ4); exact Hv).
      rewrite Hz. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK iiv_Bspan IIV_STEP.
    { iiv_awr. }
    iiv_unchanged UN5 HFr. clear HF HFr HG.
    pmkst HS.
    apply (iiv_tail ly S W mem md sp0 t tb regs0 n _ _ _ FX).
    * eapply (iiv_inv_move ly S W mem md sp0 t tb regs0 n regs mem1 md1); [exact Ht0 | exact INV | exact HJ | |].
      -- intros a Ha Hna. rewrite (UN5 a Ha (fun x => x)), (UN4 a Ha (fun x => x)), (KEPT4 a Ha Hna).
         exact (KEPT3 a Ha Hna).
      -- iiv_regs_kept HS EE ltac:(rewrite OLD4, OLD2 by lia).
    * replace (Z.to_nat (n + 1)) with (Datatypes.S nn) by lia.
      apply iiv_firstn_S; [exact Hnn | exact HFX | exact Hm].
Qed.


(* the 18 passes: by induction on the passes left *)
Lemma iiv_loop : forall k ly S (W : world SEGS) mem md sp0 t tb (regs0 : bvmap 5 word) n regs mem1 md1,
Z.of_nat k = 18 - n ->
iiv_fixed regs0 sp0 t tb ->
iiv_inv ly S W mem md sp0 t tb regs0 n regs mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + IIV_LOOP)) mem1 (seg_rom SEGS)) md1)
(iiv_post ly S W mem md sp0 tb regs0).
Proof.
induction k as [|k IH]; intros ly S W mem md sp0 t tb regs0 n regs mem1 md1 Hk FX INV.
- exfalso. destruct INV as (Hn & _). lia.
- eapply SRr_bind; [exact (iiv_body ly S W mem md sp0 t tb regs0 n regs mem1 md1 FX INV)|].
  intros W' c' _ [HP | (-> & regs' & mem' & md' & -> & Hn17 & INV')].
  + apply SRr_ret. exact HP.
  + exact (IH ly S W mem md sp0 t tb regs0 (n + 1) regs' mem' md' ltac:(lia) FX INV').
Qed.

(* what the statement's token premise gives the walk: a C string at t inside a live block, which the wrappers may
   read from any state whose sp is the frame's, and whose word tail past the terminator the musl loops read
   (cmd_heap_tail_vis: req_size k >= k, so the terminator's word ends inside the block's requested range) *)
Lemma iiv_token : forall ly S (W : world SEGS) mem md t tb sp0,
AR SEGS B ly S W mem md ->
in_blockA (ablocks B ly S) t (Z.of_nat (length tb) + 1) ->
astr_atR (aview SEGS (w_H W) mem) t tb ->
Z.of_nat (length tb) + 1 <= LMAX + 1 ->
alloc_ceiling + 80 + 2 * ESTACK <= sp0 ->
0 < t /\ Forall (fun b : byte => bv_unsigned b <> 0) tb /\ Z.of_nat (length tb) + 1 < 2 ^ 32 /\
astr_atR (aview SEGS (w_H W) mem) t tb /\ t + Z.of_nat (length tb) + 1 <= alloc_ceiling /\
(forall rq, spZ rq = sp0 - 80 -> aread_ok SEGS (2 * ESTACK) W rq mem t (Z.of_nat (length tb) + 1)) /\
atail_vis SEGS W mem (t + Z.of_nat (length tb)).
Proof.
intros ly S W mem md t tb sp0 HAR HBLK HSTR HLM Hsp.
destruct HBLK as (p & k & Hin & Hp & Hpk).
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HNZ : Forall (fun b : byte => bv_unsigned b <> 0) tb).
{ apply Forall_forall. intros b Hb Hb0. apply (proj2 HSTR). replace (Z_to_bv 8 0) with b; [exact Hb|].
  apply bv_eq. rewrite Hb0. reflexivity. }
unfold LMAX in HLM.
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hpres & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
split; [lia|]. split; [exact HNZ|]. split; [lia|]. split; [exact HSTR|]. split; [lia|].
split.
- intros rq Hrq. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W rq mem md p k t);
  [exact HAR | exact Hin | lia | lia | lia | lia].
- apply (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md p k); [exact HAR | exact Hin | lia].
Qed.

(* the caller's frame the prologue stores: ra, s0..s7 at sp0 - 8 .. sp0 - 72 *)
Definition iiv_frame_chunks : list YP09.chunk :=
[YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
 YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma iiv_frame_of_chunks : forall E m sp0 (regs0 : bvmap 5 word),
Forall (YP09.chunk_ok SEGS E m sp0) iiv_frame_chunks ->
(forall r, In r iiv_saved -> ew E (Z.to_nat r) = getr regs0 (Z_to_bv 5 r)) ->
iiv_frame m sp0 regs0.
Proof.
intros E m sp0 regs0 HC HE j r Hj.
assert (G : forall off r', In (YP09.mkChunk off (CVal 8 (SOff (Z.to_nat r') 0))) iiv_frame_chunks -> In r' iiv_saved ->
  val_mem SEGS m (sp0 + off) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r')))).
{ intros off r' Hin Hr.
  apply (val_of_chunk_ok SEGS E m sp0 off 8 (SOff (Z.to_nat r') 0)).
  - exact (proj1 (Forall_forall _ _) HC _ Hin).
  - cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact (HE r' Hr).
  - pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 r'))) as HR.
    change (bv_modulus 64) with (2 ^ 64) in HR. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HR.
  - change (Z.of_N 8) with 8. lia. }
do 9 (destruct j as [|j];
  [ cbn in Hj; injection Hj as Hr; subst r;
    lazymatch goal with |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?jj) _ _ =>
      let o := eval cbv in (-8 - 8 * Z.of_nat jj) in replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + o) by lia end;
    apply G; [unfold iiv_frame_chunks; repeat (first [left; reflexivity | right])
             | unfold iiv_saved; repeat (first [left; reflexivity | right])] |]).
destruct j; cbn in Hj; discriminate Hj.
Qed.

(* the symbolic state at the entry: the frame to be stored, the GOT word of the shadow base and the cell it names *)
Lemma iiv_seed_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md,
AR SEGS B ly S W mem md -> cmd_val_objs ->
astk_ok IS_INSTANCE_VERB_STK ly (spZ regs) ->
(forall a, spZ regs - IS_INSTANCE_VERB_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) iiv_ss_entry
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + IIV_ENTRY)) mem (seg_rom SEGS)))
/\ sh_ok SEGS iiv_Bx iiv_SH (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md HAR VOBJS Hstk Hpres.
set (sp0 := spZ regs) in *.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by exact (VOBJS 0%nat ltac:(vm_compute; lia)).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by exact (VOBJS 12%nat ltac:(vm_compute; lia)).
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
set (E := Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 0xa63f0).
{ rewrite <- V0. subst E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. }
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 0xb10b8).
{ rewrite <- V12. subst E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. }
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split; [|constructor].
rewrite restrict_mkst_fx. unfold iiv_ss_entry. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold iiv_estack, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) 0xa63f0 E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8).
    * cbn [sv_denot]. rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * change (Z.of_N 8) with 8. lia.
    * rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) 0xb10b8 E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 (SOff 32 0) SHADOW_OFF).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * unfold SHADOW_OFF. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * change (Z.of_N 8) with 8. lia.
    * rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold iiv_estack, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) 0xa63f0 E241), (VB (A_OBJ 12) 0xb10b8 E253) by lia. cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok iiv_facts]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. exact Hal16.
Qed.

Lemma iiv_img_atom : forall E (a : nat) v, img_env VAL A_LIM E -> (A_TEXT <= a < A_LIM)%nat -> VAL a = v ->
ew E a = Z_to_bv 64 v.
Proof. intros E a v HE Ha Hv. rewrite <- Hv, <- (HE a Ha). symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* the entry: the prologue, strcspn(t, " \t"), the loop set-up, then the 18 passes *)
Lemma iiv_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md t tb,
afn_pre_na SEGS B IS_INSTANCE_VERB_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 t ->
in_blockA (ablocks B ly S) t (Z.of_nat (length tb) + 1) ->
astr_atR (aview SEGS (w_H W) mem) t tb ->
Z.of_nat (length tb) + 1 <= LMAX + 1 ->
cmd_ro_ok (aview SEGS (w_H W) mem) -> cmd_val_objs ->
SRr SEGS W (cfg_at SEGS (BASE + AF_is_instance_verb) regs mem md)
(iiv_post ly S W mem md (spZ regs) tb regs).
Proof.
intros ly S W regs mem md t tb HPRE HROD H10 HBLK HSTR0 HLM HRO VOBJS.
pose proof HPRE as (HAR & Hraw & Hra4 & Hgp & Htp & Hstk & Hpres & _).
pose proof (ajournal_init_na SEGS B IS_INSTANCE_VERB_STK [] ly S W regs mem md HPRE) as HJ.
pose proof (proj1 (proj2 (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG ly S W mem md HAR))) as HGD.
set (sp0 := spZ regs) in *.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof ASAN_CEIL_range as [CR CR4]. unfold ASAN_CEIL in CR, CR4.
assert (HTS : IS_INSTANCE_VERB_STK = 8272) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (iiv_token ly S W mem md t tb sp0 HAR HBLK HSTR0 HLM ltac:(lia))
as (Ht0 & HNZ & Hlen32 & HSTR & Htc & HRDt & HTL).
pose proof (PaLibH.amem8_of_blockA SEGS B LAWS ly S W mem md t (astr_len tb) HAR HBLK ltac:(unfold astr_len; lia)) as AMt.
assert (HP0 : iiv_memP W mem sp0 t tb).
{ split; [exact HROD|]. split; [exact (iiv_roF_of_ro W mem HRO)|]. split; [exact HGD|].
  split; [exact HSTR|]. split; [exact Htc|]. split; [exact HRDt | exact HTL]. }
assert (FX : iiv_fixed regs sp0 t tb).
{ split; [exact VOBJS|]. split; [exact HNZ|]. split; [exact Ht0|]. split; [exact Hlen32|].
  split; [exact Hraw|]. split; [unfold w64, sp0, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Hgp|]. split; [exact Htp | exact AMt]. }
assert (V81 : VAL 322%nat = 0x224c0) by exact (VOBJS 81%nat ltac:(vm_compute; lia)).
assert (V109 : VAL 350%nat = 0x22d80) by exact (VOBJS 109%nat ltac:(vm_compute; lia)).
assert (V115 : VAL 356%nat = 0xa61a0) by exact (VOBJS 115%nat ltac:(vm_compute; lia)).
destruct (iiv_seed_entry W regs mem ly S md HAR VOBJS Hstk Hpres) as [HS SHOK].
remember (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HE, Eimg_low by (unfold A_TEXT; lia). change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
clear HE.
assert (Esp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at, w64. change (Z_to_bv 64 (BASE + AF_is_instance_verb)) with (Z_to_bv 64 (BASE + IIV_ENTRY)).
(* the prologue, up to strcspn(t, " \t") *)
paj_run_tok RUN HS HJ SHOK iiv_Bspan.
{ unfold iiv_ss_entry; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0); [reflexivity | rewrite Esp; lia | cbn; rewrite HTS; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as Hq1 Hq2 Hq3; subst b wlo whi; cbn [base_val] in Hrr;
                                             rewrite ?Esp in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0
| st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0 end.
destruct HR0 as (_ & _ & _ & HC0). cbn [YP09.r_chunks YP09.r_base base_val] in HC0. rewrite Esp in HC0.
assert (HFR1 : iiv_frame (mrestrict (w_H W) (ms_mem ms)) sp0 regs).
{ apply (iiv_frame_of_chunks E _ sp0 regs HC0). intros r Hr. unfold iiv_saved in Hr.
  repeat (destruct Hr as [<- | Hr]; [apply EE; reflexivity|]). destruct Hr. }
assert (HM1 : iiv_memF W (ms_mem ms) sp0 t tb regs).
{ apply iiv_memF_of; [|exact HFR1].
  apply (iiv_memP_win W mem (ms_mem ms) sp0 t tb alloc_ceiling sp0); [| lia | lia | lia | exact Ht0 | exact HP0].
  intros a Ha Hna. apply (UN1 a Ha). cbv beta. lia. }
pose proof HM1 as (HROD1 & HROF1 & HG1 & HSTR1 & _ & HRDt1 & HTLt1 & _).
pose proof HROF1 as (_ & HS11 & _ & _ & _ & HE11 & _).
pose proof (proj1 HJ) as HAR1.
assert (Hsp1 : spZ (ms_regs ms) = sp0 + -80) by (unfold spZ; rewrite Q2, Esp; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcspn) W (ms_regs ms) (ms_mem ms) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md []
  ly S _ 0 (-80) _ _ HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Q1 ltac:(intros a [])).
  apply (STRCSPN fx ly S W (ms_regs ms) (ms_mem ms) _ t A_SEPS tb iiv_seps).
  - exact HG1.
  - apply (ecall_pre_stk_at SEGS B (2 * ESTACK) IS_INSTANCE_VERB_STK sp0 [] ly S W mem md [] ly S W (ms_mem ms) _ 0
    (ms_regs ms) (-80) HJ Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    + rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    + rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Q10, (EE 10%nat 10%bv eq_refl). exact H10.
  - rewrite Q11. unfold w64. exact (iiv_img_atom E 322%nat _ HEI ltac:(unfold A_TEXT, A_LIM; lia) V81).
  - lia.
  - unfold A_SEPS. lia.
  - apply (proj1 (astr_atR_view SEGS W _ _ _)). exact HSTR1.
  - exact (iiv_seps_str W _ HROF1).
  - unfold astr_len. apply HRDt1. exact Hsp1.
  - exact AMt.
  - eapply (iiv_aread_img ly S W _ _ (ms_regs ms) A_SEPS _ RO_lit_224c0 HAR1 iiv_seps_in);
    [reflexivity | exact HS11 | unfold A_SEPS; lia | unfold A_SEPS; lia | lia | lia].
  - change (astr_len iiv_seps) with 2. apply PaLibH.amem8_of_low; unfold A_SEPS, kLowMemEnd; lia.
  - exact HTLt1.
  - exact HE11.
  - exact (iiv_romv W _ HROD1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & Hkeep).
assert (KEPT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 - 2 * ESTACK <= a < sp0 - 80) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hna. apply Hkeep; [exact Ha | lia | exact (fun H => H)]. }
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS HJ SHOK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rename HJ2 into HJ.
remember (havoc E 48 _) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD2 : forall m, (m < 48)%nat -> ew E2 m = ew E m) by (intros m Hm; rewrite HE2, ew_havoc_old by lia; reflexivity).
clear HE2.
assert (SHOK : sh_ok SEGS iiv_Bx iiv_SH E2 (mrestrict (w_H W) mem2)) by constructor.
prreg HS (10%bv : bv 5) R10.
(* the loop set-up, to the header *)
paj_run_to_tok RUNTO HS HJ SHOK iiv_Bspan IIV_LOOP.
{ iiv_awr. }
iiv_unchanged UN2 HFr. clear HF HFr HG.
pmkst HS.
assert (W32 : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD2 by lia; exact E32).
assert (W350 : ew E2 350 = Z_to_bv 64 0x22d80) by exact (iiv_img_atom E2 350%nat _ HEI2 ltac:(unfold A_TEXT, A_LIM; lia) V109).
assert (W356 : ew E2 356 = Z_to_bv 64 0xa61a0) by exact (iiv_img_atom E2 356%nat _ HEI2 ltac:(unfold A_TEXT, A_LIM; lia) V115).
apply (iiv_loop 18 ly S W mem md sp0 t tb regs 0 _ _ _ eq_refl FX).
split; [lia|]. split; [exact HJ|]. split.
{ eapply iiv_memF_kept; [| lia | lia | exact Ht0 |].
  - intros a Ha _. exact (UN2 a Ha (fun x => x)).
  - eapply iiv_memF_kept; [exact KEPT2 | lia | lia | exact Ht0 | exact HM1]. }
split; [unfold spZ; iiv_sreg HS; rewrite OLD2 by lia;
  rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 2)), Esp, iiv_wrap_add; apply unsigned_lit_small; lia|].
split; [iiv_sreg HS; rewrite OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp|].
split; [iiv_sreg HS; rewrite OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp|].
split; [iiv_sreg HS; rewrite OLD2 by lia; rewrite (EE 10%nat 10%bv eq_refl); exact H10|].
split; [iiv_sreg HS; cbn [ms_regs restrict mkst] in R10; rewrite <- R10, HQ2, iiv_cspn_t; reflexivity|].
split; [iiv_sreg HS; rewrite W350; reflexivity|].
split; [iiv_sreg HS; reflexivity|].
split; [iiv_sreg HS; rewrite W356; reflexivity|].
split; [iiv_sreg HS; rewrite W32, W356; apply bv_eq; vm_compute; reflexivity|].
split; [iiv_sreg HS; apply bv_eq; vm_compute; reflexivity|].
split; [|reflexivity].
intros r Hr.
assert (Hc4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc4 as [-> | [-> | [-> | ->]]]; iiv_sreg HS; rewrite OLD2 by lia; apply EE; reflexivity.
Qed.

Theorem is_instance_verb_ok : tis_instance_verb_spec B MT.
Proof.
intros ly S W regs mem md t tb HPRE HROD H10 Ht64 HBLK HSTR HLM HRO VOBJS HEV.
eapply SRr_mono; [exact (iiv_entry ly S W regs mem md t tb HPRE HROD H10 HBLK HSTR HLM HRO VOBJS)|].
intros W' c' _ (regs' & mem' & md' & -> & HJ & HP & HR). unfold apost_base.
exists ly, S, regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [exact HR|]. split; [apply Permutation_refl|]. split; reflexivity.
Qed.
End e.
End f.
End d.
