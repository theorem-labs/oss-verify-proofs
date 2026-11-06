(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment E of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530 .. the jal of rec_clear at 0x86584: the frame, the size test, the shadow base), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s10.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the seed and the run from the entry) and A/ACh6.v (a segment closed by the statement of the point it leaves to). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- n-byte fields read through a reader: a readable range holds some value (the plain proof's word4_g / word8_g,
   lib/Prog/SlotRec.v:124-158), a 4-byte one also as a signed int ---- *)
Lemma le_pow_S : forall n, 2 ^ (8 * Z.of_nat (Datatypes.S n)) = 256 * 2 ^ (8 * Z.of_nat n).
Proof.
intros n. rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat n)) with (8 + 8 * Z.of_nat n) by lia.
rewrite Z.pow_add_r by lia. reflexivity.
Qed.
Lemma le_byte_cons0 : forall b v n, 0 <= b < 256 -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  le_byte (b + 256 * v) (Datatypes.S n) 0 = b.
Proof.
intros b v n Hb Hv. unfold le_byte. rewrite le_pow_S.
rewrite (Z.mod_small (b + 256 * v)) by lia.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mul_comm 256 v), Z_mod_plus_full. apply Z.mod_small. exact Hb.
Qed.
Lemma le_byte_consS : forall b v n k, 0 <= b < 256 -> 0 <= v < 2 ^ (8 * Z.of_nat n) -> (k < n)%nat ->
  le_byte (b + 256 * v) (Datatypes.S n) (Datatypes.S k) = le_byte v n k.
Proof.
intros b v n k Hb Hv Hk. unfold le_byte. rewrite le_pow_S.
rewrite (Z.mod_small (b + 256 * v)) by lia. rewrite (Z.mod_small v) by lia.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
rewrite Z.pow_add_r by lia.
rewrite <- Z.div_div by first [lia | apply Z.pow_pos_nonneg; lia].
change (2 ^ 8) with 256.
replace ((b + 256 * v) / 256) with v; [reflexivity|].
apply (Z.div_unique (b + 256 * v) 256 v b); [left; lia | lia].
Qed.
Lemma le_aval_exists : forall (rd : reader) n a,
  (forall k, (k < n)%nat -> exists b, rd (a + Z.of_nat k) = Some b /\ 0 <= b < 256) ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ aval_mem rd a n v.
Proof.
intros rd n. induction n as [|n IH]; intros a H.
- exists 0. split; [change (2 ^ (8 * Z.of_nat 0)) with 1; lia|]. intros k Hk. exfalso. lia.
- destruct (H 0%nat ltac:(lia)) as (b & Hb & Rb).
  assert (H1 : forall k, (k < n)%nat -> exists c, rd (a + 1 + Z.of_nat k) = Some c /\ 0 <= c < 256).
  { intros k Hk. destruct (H (Datatypes.S k) ltac:(lia)) as (c & Hc & Rc). exists c. split; [|exact Rc].
    rewrite <- Hc. f_equal. lia. }
  destruct (IH (a + 1) H1) as (v & Rv & Hv).
  exists (b + 256 * v). rewrite le_pow_S. split; [lia|].
  intros k Hk. destruct k as [|k].
  + rewrite (le_byte_cons0 b v n Rb Rv). exact Hb.
  + rewrite (le_byte_consS b v n k Rb Rv ltac:(lia)).
    replace (a + Z.of_nat (Datatypes.S k)) with (a + 1 + Z.of_nat k) by lia. exact (Hv k ltac:(lia)).
Qed.
Lemma le_aval_signed32 : forall rd a u, 0 <= u < 2 ^ 32 -> aval_mem rd a 4 u ->
  exists s, -2 ^ 31 <= s < 2 ^ 31 /\ aval_mem rd a 4 s.
Proof.
intros rd a u Hu H. destruct (Z_lt_le_dec u (2 ^ 31)) as [Hl|Hl].
- exists u. split; [lia | exact H].
- exists (u + -1 * 2 ^ 32). split; [lia|].
  intros k Hk. rewrite (H k Hk). f_equal.
  exact (eq_sym (f_equal (fun z => Z.shiftr z (8 * Z.of_nat k) mod 256) (Z_mod_plus_full u (-1) (2 ^ (8 * Z.of_nat 4))))).
Qed.
Lemma le_byte_0_loc : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma le_aval_zero : forall rd a n b w, zero_atA rd a n -> a <= b -> b + Z.of_nat w <= a + n -> aval_mem rd b w 0.
Proof.
intros rd a n b w HZ H1 H2 k Hk. rewrite le_byte_0_loc.
replace (b + Z.of_nat k) with (a + (b - a + Z.of_nat k)) by lia. apply HZ. lia.
Qed.
Lemma le_zero_kept : forall rd rd' lo hi a n, kept_out rd rd' lo hi -> zero_atA rd a n -> 0 <= a -> a + n <= lo ->
  lo < 2 ^ 64 -> zero_atA rd' a n.
Proof. intros rd rd' lo hi a n HK HZ Ha Hn Hlo i Hi. rewrite (HK (a + i)) by lia. exact (HZ i Hi). Qed.
(* a byte the image's ROM holds is readable through every view (YP09.v mbyte falls back on seg_rom) *)
Lemma le_rd_byte : forall segs H (mem : word -> option byte) a, seg_rom segs (Z_to_bv 64 a) <> None ->
  exists b, aview segs H mem a = Some b /\ 0 <= b < 256.
Proof.
intros segs H mem a Hr. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|] eqn:E.
- exists (bv_unsigned b). split; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
- destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:E2; [|exfalso; exact (Hr eq_refl)].
  exists (bv_unsigned b). split; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* ---- the recorder as GI_cmdA leaves it (the plain proof's gi_rep, lib/Prog/SlotRec.v:174-209): no call, the spill
   empty, no answer, no reply, nreplies 0; refuse, code, state and host whatever g_rec holds ---- *)
Section rb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma le_rec_entry : forall ly S (rd : reader),
  zero_atA rd (A_G_REC + 8) 4 -> zero_atA rd (A_G_REC + 912) 12 -> zero_atA rd (A_G_REC + 928) 16 ->
  zero_atA rd A_REC_SPILL 8 ->
  (forall a, A_G_REC <= a < A_G_REC + 960 -> exists b, rd a = Some b /\ 0 <= b < 256) ->
  exists R, rec_repA B ly S rd R [] /\ r_calls R = [] /\ r_answer R = None /\ r_reply R = None /\
    r_nreplies R = 0 /\ r_spill R = (0, []).
Proof.
intros ly S rd Z1 Z2 Z3 Z4 HRD.
assert (RD : forall o n, 0 <= o -> o + Z.of_nat n <= 960 ->
  forall k, (k < n)%nat -> exists b, rd (A_G_REC + o + Z.of_nat k) = Some b /\ 0 <= b < 256).
{ intros o n Ho Hn k Hk. apply HRD. lia. }
destruct (le_aval_exists rd 4 (A_G_REC + OFF_REFUSE) (RD OFF_REFUSE 4%nat ltac:(unfold OFF_REFUSE; lia)
  ltac:(unfold OFF_REFUSE; lia))) as (u0 & Ru0 & Hu0).
destruct (le_aval_exists rd 4 (A_G_REC + OFF_CODE) (RD OFF_CODE 4%nat ltac:(unfold OFF_CODE; lia)
  ltac:(unfold OFF_CODE; lia))) as (u1 & Ru1 & Hu1).
destruct (le_aval_exists rd 8 (A_G_REC + OFF_STATE) (RD OFF_STATE 8%nat ltac:(unfold OFF_STATE; lia)
  ltac:(unfold OFF_STATE; lia))) as (st & Rst & Hst).
destruct (le_aval_exists rd 8 (A_G_REC + OFF_HOST) (RD OFF_HOST 8%nat ltac:(unfold OFF_HOST; lia)
  ltac:(unfold OFF_HOST; lia))) as (hs & Rhs & Hhs).
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Ru0, Ru1.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rst, Rhs.
destruct (le_aval_signed32 rd _ u0 Ru0 Hu0) as (rf & Rrf & Hrf).
destruct (le_aval_signed32 rd _ u1 Ru1 Hu1) as (cd & Rcd & Hcd).
exists (RState rf cd [] (0, []) None 0 None st hs).
split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
exists (RLay [] [] None None). split; [|intros pn; cbn; tauto].
unfold arep_at. split; [unfold A_G_REC; reflexivity|]. split; [unfold A_REC_SPILL; reflexivity|].
split; [unfold iv_apart, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE; lia|].
split.
{ unfold ag1_calls. cbn [r_calls l_calls r_spill l_spill length snd].
  split; [lia|]. split; [reflexivity|].
  split; [apply (le_aval_zero rd _ _ _ _ Z1); unfold OFF_NCALLS; lia|].
  split; [intros i c P Hc; destruct i; cbn [nth_error] in Hc; discriminate Hc|].
  split; [|constructor].
  unfold acall_at. cbn [fst snd length map].
  split; [unfold REC_FN_COUNT; lia|]. split; [lia|]. split; [reflexivity|].
  split; [apply (le_aval_zero rd _ _ _ _ Z4); unfold CALL_OFF_FN; lia|].
  split; [apply (le_aval_zero rd _ _ _ _ Z4); unfold CALL_OFF_NARGS; lia|].
  split; [constructor|]. intros k s pn Hs; destruct k; cbn [nth_error] in Hs; discriminate Hs. }
split; [cbn [r_answer l_answer aanswer_at]; apply (le_aval_zero rd _ _ _ _ Z2); unfold OFF_ANSWER; lia|].
split; [cbn [r_reply l_reply areply_at]; split; apply (le_aval_zero rd _ _ _ _ Z3); unfold OFF_REPLY, OFF_REPLY_SIZE; lia|].
split.
{ unfold ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host].
  split; [exact Hrf|]. split; [exact Hcd|].
  split; [apply (le_aval_zero rd _ _ _ _ Z2); unfold OFF_NREPLIES; lia|].
  split; [exact Hst|]. split; [exact Hhs|]. lia. }
unfold ag1_own. cbn [lay_blocks l_calls l_spill l_answer l_reply oblk concat app map].
split; [constructor | intros pn []].
Qed.
End rb.

(* the events of the whole call are never negative; stated over the pair ev_msgs returns, so that no destruct of
   ev_msgs 32 R_ENTRY pl generalizes a hypothesis over it (that proof term took the kernel over 60 s to check) *)
Lemma le_pair_ge0 : forall x : Z * rstate, 0 <= fst x ->
  0 <= (let '(k, Rf) := x in EV_REC_CLEAR R_ENTRY + k + EV_REC_CLEAR Rf).
Proof.
intros [k Rf] H. cbn [fst] in H. pose proof (EV_REC_CLEAR_ge0 R_ENTRY). pose proof (EV_REC_CLEAR_ge0 Rf). lia.
Qed.
Lemma le_ev_ltoi_ge0 : forall pl, 0 <= EV_LTOI pl.
Proof. intros pl. exact (le_pair_ge0 (ev_msgs 32 R_ENTRY pl) (ev_msgs_ge0 32 R_ENTRY pl)). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the symbolic entry state: every register is its own atom, atom 32 is the shadow base; regions: the 256-byte frame
   below the entry sp (atom 2), the GOT word of the shadow cell (A_OBJ 0 = 0xa5f50 -> A_OBJ 12) and the shadow cell
   itself (A_OBJ 12 = 0xb0c38 -> atom 32). No inline check: no shadow entry. *)
Definition LEx : sv := SOff 32 0.
Definition LEspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition le_regions : smem := [ stack_region 256; got_regionP; bcell_regionP 32 ].
Definition le_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF LT_SB LT_SB 0) ] [] [].
Definition ss_le : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms le_regions None le_facts.
Definition le_SH : list shent := [].
Definition le_extra : list word := [Z_to_bv 64 LT_SB].
Definition le_E (regs : bvmap 5 word) : env := Eimg (Ereg regs le_extra).

Lemma le_ew_obj : forall E i v, cmd_val_objs -> img_env VAL A_LIM E -> (i < length cmd_objs)%nat ->
  nth i cmd_objs 0 = v -> (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = Z_to_bv 64 v.
Proof.
intros E i v HOBJ HE Hi Hv Hl. pose proof (HE (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT in *; lia)) as H.
assert (HV : VAL (A_OBJ i) = v) by (rewrite (HOBJ i Hi); exact Hv).
rewrite HV in H. pose proof (pa_val_range (A_OBJ i)) as R. rewrite HV in R.
apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* a word the entry saved in its frame, read back from the stack region's chunk *)
Lemma le_saved_one : forall (W : world SEGS) (regs : bvmap 5 word) E ss ms rg (r : bv 5) sp off,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some rg -> YP09.r_base rg = Some 2%nat ->
  In (YP09.mkChunk (- off) (CVal 8 (SOff (Z.to_nat (bv_unsigned r)) 0))) (YP09.r_chunks rg) ->
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) -> bv_unsigned (ew E 2) = sp ->
  rdword (rdW W (ms_mem ms)) (sp - off) = Some (bv_unsigned (getr regs r)).
Proof.
intros W regs E ss ms rg r sp off HS Hi Hb Hin EEo Hsp.
assert (Er : ew E (Z.to_nat (bv_unsigned r)) = getr regs r).
{ apply EEo. pose proof (bv_unsigned_in_range 5 r). rewrite Z2Nat.id by lia. reflexivity. }
pose proof (bv_unsigned_in_range 64 (getr regs r)) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) 0 rg 2 (- off) 8
  (SOff (Z.to_nat (bv_unsigned r)) 0) sp (bv_unsigned (getr regs r)) HS Hi Hb Hin Hsp) as Hv.
cbn [ms_mem restrict] in Hv.
replace (sp - off) with (sp + - off) by lia.
apply (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact Rr].
apply Hv.
- cbn [sv_denot]. rewrite Er, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Rr.
- lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk's hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
(* placeholder: no lemma of lib/B/Prog/CmdRecFacts.v gives it. Every byte of g_rec, record.spill and g_quitting is
   a byte of the image's segments with a ROM byte, so it is readable through every view (the plain proof's
   g_present, lib/Prog/SlotRec.v:124-158). cmd_img_facts gives only in_img (cif_prog_img); seg_rom also needs the
   segment readable and its bytes in the snapshot (LPS RiscvSemantics.v memory_read), which cif_rom_some states for
   the read-only segments only. At assembly over the pinned image: lib/B/YB13.v:147 tfib_rom_all
   (0x10000 <= a < 0x606000), the B twin of the A walk's same placeholder (lib/A/AB13.v:146). *)
Hypothesis cmd_prog_rd : forall a, inFP cmd_PG a -> seg_rom SEGS (Z_to_bv 64 a) <> None.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* nothing spent at the entry: the whole of EV_LTOI still to come, metered at most LT_U each (XM_LTOI) *)
Lemma le_bud0 : forall cx : lcx, lt_bud MT cx (x_S cx) 0 0 (EV_LTOI (x_pl cx)).
Proof.
intros cx. pose proof (le_ev_ltoi_ge0 (x_pl cx)) as N1. unfold lt_bud.
split; [lia|]. split; [exact N1|]. split; [lia|].
split; [exact (mo_le_refl MT MTL (x_S cx))|]. split; [lia|].
rewrite Z.add_0_l. unfold XM_LTOI, LT_U. apply Z.le_refl.
Qed.

Lemma le_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md,
cmd_val_objs ->
AR SEGS B ly S W mem md ->
astk_ok LTOI_STK ly (spZ regs) ->
(forall a, spZ regs - LTOI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (le_E regs) ss_le
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS)))
/\ sh_ok SEGS LEx le_SH (le_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem ly S md HOBJ HAR Hstk Hpres.
assert (WS : LTOI_STK = 32768) by reflexivity. rewrite WS in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := le_E regs).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold le_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs le_extra) k)
  by (intros k Hk; subst E; unfold le_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 LT_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 0xa5f50)
  by (apply le_ew_obj; [exact HOBJ | exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 0xb0c38)
  by (apply le_ew_obj; [exact HOBJ | exact HEI | vm_compute; lia | reflexivity | unfold A_OBJ, A_LIM; lia]).
assert (V0 : VAL (A_OBJ 0) = 0xa5f50) by (rewrite (HOBJ 0%nat ltac:(vm_compute; lia)); reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb0c38) by (rewrite (HOBJ 12%nat ltac:(vm_compute; lia)); reflexivity).
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_le. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold le_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold le_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) 0xa5f50 EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa5f50 0 8 (SOff (A_OBJ 12) 0) 0xb0c38);
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 12) 0xb0c38 EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xb0c38 0 8 (SOff 32 0) LT_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold LT_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold le_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) 0xa5f50 EO0), (VB (A_OBJ 12) 0xb0c38 EO12) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 Hstk0. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [le_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold LT_SB; lia).
    unfold LT_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, le_SH. apply Forall_nil.
Qed.

(* ---- segment E: from the entry 0x86530 to the jal of rec_clear at 0x86584; the continuation is taken at every FP
   state and applied at the entry's (nothing in this stretch touches the FP state) ---- *)
Theorem lt_seg_E : LTA_RC1 B MT -> LT_ENTRY_stmt B MT.
Proof.
intros HRC1 cx HBASE HFRM.
destruct cx as [ly S W regs mem md ch p n pl j].
pose proof HBASE as HB0. unfold lt_base in HB0.
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_p x_n x_pl x_j] in HB0.
destruct HB0 as (HPRE & HROD & HRO & HOBJ & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
cbn [x_W x_regs x_mem x_md x_ly x_S].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE'. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
rewrite WS in Hstk0, Hslo, Hbot.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
destruct (le_entry W regs mem ly S md HOBJ HAR Hstk Hpres) as [HS SHOK].
pose proof (ajournal_init SEGS B LTOI_STK cmd_PG ly S W regs mem md ch HPRE) as HJ.
assert (EL : forall k, (k < A_TEXT)%nat -> ew (le_E regs) k = ew (Ereg regs le_extra) k)
  by (intros k Hk; unfold le_E; apply Eimg_low; exact Hk).
assert (HEI : img_env VAL A_LIM (le_E regs)) by (unfold le_E; apply Eimg_env).
remember (le_E regs) as E eqn:HE.
assert (EEo : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (apply EEo; reflexivity).
assert (E11 : ew E 11 = getr regs 11) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 LT_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
unfold cfg_at.
(* 0x86530 .. 0x8656c: the frame (sp -= 256, ra and s0 .. s11 saved at sp + 248 .. sp + 152), s8 := n, a1 := n >> 26 *)
paj_run_tok RUN HS HJ SHOK LEspan.
{ awr_ok_tac; exact Usp. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP0 : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 256) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 256 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
clear HF HFr HG. rename ms into ms1.
(* 0x86570: bnez a1; the pre-condition's n < 2^26 rules out the refusal at 0x86b10 *)
psrr_branch_tok RUN BR HS SHOK LEspan.
{ exfalso. rewrite branch_ne_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom E 11 n) in Hc by first [rewrite E11; exact H11 | lia].
  rewrite !U_lit in Hc by lia.
  change (Z.land 26 63) with 26 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small n (2 ^ 26)) in Hc by lia.
  vm_compute in Hc. discriminate Hc. }
(* 0x86574 .. 0x86584: s7 := p, s9 := the shadow base through its GOT word; then the jal of rec_clear *)
paj_run_tok RUN HS HJ SHOK LEspan.
{ awr_ok_tac; exact Usp. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - 256) (spZ regs))
by (intros a Ha Hn; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 256 <= a < spZ regs) Hfr);
  [ exact (KEEP0 a Ha Hn)
  | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
rewrite (SIGP CS_rec_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_rec_clear) with AF_rec_clear by (vm_compute; reflexivity).
(* the frame *)
assert (HspT : spZ (ms_regs ms) = spZ regs - 256).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. lia. }
lazymatch type of HS with st_ok _ _ ?ss1 _ =>
  let l := eval vm_compute in (nth_error (ss_mem ss1) 0) in
  lazymatch l with Some ?rg => assert (HRG : nth_error (ss_mem ss1) 0 = Some rg) by reflexivity end end.
assert (HFRAME : lt_frame B (mkLCX ly S W regs mem md ch p n pl j) ly S W (ms_regs ms) (ms_mem ms) mdv 0).
{ unfold lt_frame. split; [exact HJ|]. split; [unfold x_sp1, LT_FRAME; cbn [x_regs]; exact HspT|].
  split; [rewrite P3, E3; reflexivity|]. split; [rewrite P4, E4; reflexivity|].
  unfold lt_saved, x_sp0. cbn [x_regs]. intros i r Hi. unfold LT_SAVED in Hi.
  do 13 (destruct i as [|i];
    [ cbn [nth_error] in Hi; injection Hi as Hr; subst r;
      apply (le_saved_one W regs E _ ms _ _ (spZ regs) _ HS HRG eq_refl);
        [cbn [In YP09.r_chunks]; repeat first [left; reflexivity | right] | exact EEo | exact Usp]
    | ]).
  destruct i; cbn [nth_error] in Hi; discriminate Hi. }
(* the recorder as GI_cmdA leaves it, at the call *)
assert (Hlo : 0x606000 <= spZ regs - 256 < 2 ^ 64) by lia.
pose proof HGI as (Z1 & Z2 & Z3 & Z4 & Z5).
unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Z1, Z2, Z3, Z4, Z5.
assert (Z1' : zero_atA (rdW W (ms_mem ms)) (A_G_REC + 8) 4)
  by (unfold A_G_REC; exact (le_zero_kept _ _ _ _ _ _ KEEP Z1 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (Z2' : zero_atA (rdW W (ms_mem ms)) (A_G_REC + 912) 12)
  by (unfold A_G_REC; exact (le_zero_kept _ _ _ _ _ _ KEEP Z2 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (Z3' : zero_atA (rdW W (ms_mem ms)) (A_G_REC + 928) 16)
  by (unfold A_G_REC; exact (le_zero_kept _ _ _ _ _ _ KEEP Z3 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (Z4' : zero_atA (rdW W (ms_mem ms)) A_REC_SPILL 8)
  by (unfold A_REC_SPILL; exact (le_zero_kept _ _ _ _ _ _ KEEP Z4 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (Z5' : zero_atA (rdW W (ms_mem ms)) A_G_QUITTING 4)
  by (unfold A_G_QUITTING; exact (le_zero_kept _ _ _ _ _ _ KEEP Z5 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (HRD : forall a, A_G_REC <= a < A_G_REC + 960 -> exists b, rdW W (ms_mem ms) a = Some b /\ 0 <= b < 256).
{ intros a Ha. apply le_rd_byte. apply cmd_prog_rd. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; lia]. }
destruct (le_rec_entry B ly S (rdW W (ms_mem ms)) Z1' Z2' Z3' Z4' HRD)
  as (R & HREP & Hcalls & Hans & Hrep & Hnr & Hspill).
assert (HQ0 : aval_mem (rdW W (ms_mem ms)) A_G_QUITTING 4 0)
  by (apply (le_aval_zero _ A_G_QUITTING 4 A_G_QUITTING 4 Z5'); lia).
assert (HREC : lt_rec B (mkLCX ly S W regs mem md ch p n pl j) ly S W (ms_mem ms) R [] 0 []).
{ unfold lt_rec. split; [exact HREP|]. split; [exact Hspill|]. split; [rewrite Hcalls; cbn; lia|].
  split; [exact HQ0|]. split; [lia|].
  unfold x_bl0. cbn [x_ly x_S app]. rewrite app_nil_r. apply Permutation_refl. }
(* nothing spent yet: the whole of EV_LTOI still to come (le_bud0) *)
pose proof (le_bud0 (mkLCX ly S W regs mem md ch p n pl j)) as HBUD.
assert (P1' : getr (ms_regs ms) 1 = w64 (BASE + LO_RC1RA)) by (rewrite P1; reflexivity).
assert (P25' : getr (ms_regs ms) 25 = w64 LT_SB) by (rewrite P25, E32; reflexivity).
assert (P23' : getr (ms_regs ms) 23 = w64 p) by (rewrite P23, E10; exact H10).
assert (P24' : getr (ms_regs ms) 24 = w64 n) by (rewrite P24, E11; exact H11).
assert (P8' : getr (ms_regs ms) 8 = getr regs 8) by (rewrite P8, E8; reflexivity).
exact (HRC1 fx (mkLCX ly S W regs mem md ch p n pl j) ly S W (ms_regs ms) (ms_mem ms) mdv R HBASE HFRM HFRAME
  P1' P25' P23' P24' P8' HREC Hcalls Hans Hrep Hnr HBUD).
Qed.
Print Assumptions lt_seg_E.

End e.
End f.
End d.
