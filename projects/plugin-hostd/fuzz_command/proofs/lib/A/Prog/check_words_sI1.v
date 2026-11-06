(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 556 of its 663 lines of code are new or changed and 1553 lines of the source are left out. *)
(* check_words' ASan walk, segment I1 (check_words_d.v): the head of the item loop and its latch.
     seg_I1h  IH 0x161c [0x87b00] .. IK 0x1654 [0x87b38]: the inline check of the template byte at s2, `beqz` on it
              (zero: the template is done, on to D 0x17ac [0x87c90]), the strspn wrapper on (s2, " "), s2 += its
              answer, the inline check of the byte at the new s2.
     seg_I1l  IL 0x174c [0x87c30] .. 0x1768 [0x87c4c]: the inline check of call->nargs (s3 = its shadow byte, s11 =
              &call->nargs), a + 1, the two argument cursors move on by 8, `blt a+1 nargs` back to IH, else on to D.
   Each run is the token engine's (PaShadow.v) over the position-abstract listing; the strspn call goes through
   check_words_art.v's aj_strspn_at; memory the segment never writes is read at the current state from the entry
   fact (cw_ent) and the journal. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_art check_words_asm check_words_ki.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the template parse: one step of tpl_items_a consumes at least one byte, so any fuel above the length agrees *)
Lemma cw_spn_le : forall set s, (PSpn.spn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [PSpn.spn_len length]; [lia|]. destruct (PSpn.in_set set x); lia. Qed.
Lemma cw_step_pos : forall s, s <> [] ->
  (1 <= PSpn.spn_len CW_SP1 s + PCspn.cspn_len CW_SP1 (skipn (PSpn.spn_len CW_SP1 s) s))%nat.
Proof.
intros s Hs. destruct s as [|x s']; [congruence|]. cbn [PSpn.spn_len].
destruct (PSpn.in_set CW_SP1 x) eqn:Hx; [lia|]. cbn [skipn PCspn.cspn_len].
unfold PSpn.in_set in Hx. rewrite Hx. lia.
Qed.
Lemma cw_fuel : forall f1 f2 s, (length s < f1)%nat -> (length s < f2)%nat -> tpl_items_a f1 s = tpl_items_a f2 s.
Proof.
induction f1 as [|f1 IH]; intros f2 s H1 H2; [lia|]. destruct f2 as [|f2]; [lia|].
destruct s as [|x s']; [reflexivity|].
pose proof (cw_step_pos (x :: s') ltac:(discriminate)) as P.
set (s1 := skipn (PSpn.spn_len CW_SP1 (x :: s')) (x :: s')) in *.
set (r := skipn (PCspn.cspn_len CW_SP1 s1) s1) in *.
assert (Hr : (length r < length (x :: s'))%nat) by (subst r s1; rewrite !length_skipn; cbn [length] in *; lia).
change (tpl_items_a (S f1) (x :: s')) with (item_of_a s1 :: tpl_items_a f1 r).
change (tpl_items_a (S f2) (x :: s')) with (item_of_a s1 :: tpl_items_a f2 r).
f_equal. apply IH; lia.
Qed.
Lemma cw_parse_step : forall s, s <> [] ->
  cw_parse s = item_of_a (skipn (PSpn.spn_len CW_SP1 s) s) ::
    cw_parse (skipn (PCspn.cspn_len CW_SP1 (skipn (PSpn.spn_len CW_SP1 s) s)) (skipn (PSpn.spn_len CW_SP1 s) s)).
Proof.
intros s Hs. destruct s as [|x s']; [congruence|].
pose proof (cw_step_pos (x :: s') ltac:(discriminate)) as P.
set (s1 := skipn (PSpn.spn_len CW_SP1 (x :: s')) (x :: s')) in *.
set (r := skipn (PCspn.cspn_len CW_SP1 s1) s1) in *.
assert (Hr : (length r < length (x :: s'))%nat) by (subst r s1; rewrite !length_skipn; cbn [length] in *; lia).
unfold cw_parse.
change (tpl_items_a (S (length (x :: s'))) (x :: s')) with (item_of_a s1 :: tpl_items_a (length (x :: s')) r).
f_equal. apply cw_fuel; lia.
Qed.
Lemma cw_U_add : forall E x y vx vy, U E x = vx -> U E y = vy -> 0 <= vx + vy < 2 ^ 64 ->
  U E (SAlu ALU_ADD x y) = vx + vy.
Proof. intros E x y vx vy Hx Hy R. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma cw_o16 : forall s1 s0, s1 mod 32 = 0 -> s0 mod 16 = 0 -> (s1 - s0) mod 16 = 0.
Proof.
intros s1 s0 H1 H0. pose proof (Z.div_mod s1 32 ltac:(lia)) as D1. pose proof (Z.div_mod s0 16 ltac:(lia)) as D0.
rewrite H1 in D1. rewrite H0 in D0. replace (s1 - s0) with ((2 * (s1 / 32) - s0 / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma cw_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : x / 8 <= x' / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (x' + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) ltac:(lia)).
pose proof (R8 (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) ltac:(lia)). lia.
Qed.

Lemma cw_den_off : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma cw_reg_off : forall E (regs' : bvmap 5 word) n (r : bv 5) v off,
  ew E n = Z_to_bv 64 v -> getr regs' r = sv_denot E (SOff n off) -> getr regs' r = Z_to_bv 64 (v + off).
Proof. intros E regs' n r v off Hn H. rewrite H. apply cw_den_off. exact Hn. Qed.
Lemma cw_reg_same : forall E (regsc regs' : bvmap 5 word) n (r : bv 5),
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) -> Z.of_nat n = bv_unsigned r ->
  getr regs' r = sv_denot E (SOff n 0) -> getr regs' r = getr regsc r.
Proof. intros E regsc regs' n r EV Hn H. rewrite H. cbn [sv_denot]. rewrite (EV n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma cw_EV_ewset : forall E k w (regsc : bvmap 5 word), (32 <= k)%nat ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) ->
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ewset E k w) n = getr regsc r.
Proof.
intros E k w regsc Hk H n r Hr. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite ew_ewset_other by lia. exact (H n r Hr).
Qed.
Lemma cw_EV_havoc : forall E k ws (regsc : bvmap 5 word), (32 <= k)%nat ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) ->
  forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (havoc E k ws) n = getr regsc r.
Proof.
intros E k ws regsc Hk H n r Hr. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite ew_havoc_old by lia. exact (H n r Hr).
Qed.
Ltac cw_EV EV := repeat first [apply cw_EV_ewset; [lia|] | apply cw_EV_havoc; [lia|]]; exact EV.
Ltac cw_ew_old := repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
Lemma cw_lt_off : forall E n m c x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x -> 0 <= c -> x + c < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n c)) (sv_denot E (SOff m 0)) = (x + c <? y).
Proof.
intros E n m c x y Hn Hm Hx Hc Hxc Hy. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n c))) with (Sg E (SOff n c)).
change (bv_signed (sv_denot E (SOff m 0))) with (Sg E (SOff m 0)).
rewrite !S_SOff, Hn, Hm, !unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cw_eq0_lit : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v Hn Hv. rewrite branch_eq_U, (U_atom E n v Hn Hv). reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* ---------------------------------------------------------------------------------------------------------- *)
(* the journal of the walk at a point of call c's item loop *)
#[local] Notation CWJ e pos lyc Sc Wc memc mdc :=
  (ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
     lyc Sc Wc memc mdc EV_JOINED).

Lemma cw_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hv].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
(* a run whose regions have no write window leaves every byte as it was *)
Lemma cw_kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hw a Ha. apply (kept_of_frame (segs:=SEGS) E rs H m m' (fun _ => False) Hf); [|exact Ha|tauto].
intros b wlo whi a' Hin Hr. unfold windows in Hin. apply in_map_iff in Hin as (r & Hr' & Hin').
rewrite forallb_forall in Hw. specialize (Hw r Hin'). apply Z.leb_le in Hw. injection Hr' as <- <- <-. lia.
Qed.
(* call c's argument count at the current state: rec_repA at the entry and the journal's image clause *)
Lemma cw_nargs_now : forall e pos lyc Sc Wc memc mdc c fn args, cw_ent B MT e -> CWJ e pos lyc Sc Wc memc mdc ->
  0 <= c -> nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args) ->
  aval_mem (rdW Wc memc) (A_G_REC + 16 + 56 * c + 4) 4 (Z.of_nat (length args)).
Proof.
intros e pos lyc Sc Wc memc mdc c fn args Hent HJ Hc0 Hnth.
pose proof (cw_ent_rec B MT e Hent) as (Q & (_ & _ & _ & (Hl & HlQ & _ & Hcalls & _) & _) & _).
assert (Hlt : (Z.to_nat c < length (r_calls (e_R e)))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
destruct (nth_error (l_calls Q) (Z.to_nat c)) as [P|] eqn:HP.
2: { exfalso. apply nth_error_None in HP. lia. }
destruct (Hcalls _ _ _ Hnth HP) as ((_ & _ & _ & _ & Hna & _) & _). cbn [snd] in Hna.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros i Hi. specialize (Hna i Hi).
replace (A_G_REC + 16 + 56 * c + 4 + Z.of_nat i)
  with (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_NARGS + Z.of_nat i)
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
assert (Hin : inFP cmd_PG (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (Z.to_nat c) + CALL_OFF_NARGS + Z.of_nat i)).
{ exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd].
  unfold OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS. lia. }
destruct (cmd_prog_unowned _ Hin) as (Himg & Hno & Hne).
rewrite (F3 _ Himg Hno Hne (fp_spares_closed [] _ sink_closed_nil (inFP_nil _))). exact Hna.
Qed.

(* the read-only bytes the runtime entries read, at the current state: the entry's arodata_okP and the journal's
   image clause *)
Lemma cw_arodata_now : forall e pos lyc Sc Wc memc mdc k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros e pos lyc Sc Wc memc mdc k Hent HJ a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hg)]).
rewrite (cw_img_kept B e lyc Sc Wc memc mdc pos k a HJ Himg Ho He).
pose proof Hent as (_ & _ & HROD & _). exact (HROD a Hro Ho He).
Qed.

(* the seeds. Bx = s7 (atom 23) holds the shadow base CW_SB; the template cursor s2 is atom 18, &call->nargs is
   s11 (atom 27) and s3 is its shadow byte's address. *)
Definition IBx : sv := SOff 23 0.
Definition IBspan : Z * Z := (CW_SB, CW_SB + 2 ^ 44 - 1).
(* the latch: atom 32 is nargs, read through the one region at s11 *)
Definition i1_shx27 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0) (SLit 3)) (SOff 23 0).
Definition i1l_reg : YP09.region := YP09.mkRegion (Some 27%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition i1l_facts : facts :=
  mkFacts [ (23%nat, mkAF CW_SB CW_SB 0); (27%nat, mkAF (A_G_REC + 20) (A_G_REC + 20 + 56 * 15) 0);
            (32%nat, mkAF 0 6 0) ] [] [].
Definition ssL : sstate := mkSS CW_PC_IL (sr_set sr_atoms (19%bv : bv 5) i1_shx27) [i1l_reg] None i1l_facts.
(* the head: atom 32 is the template byte at s2 *)
Definition i1h_reg : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition i1h_facts : facts :=
  mkFacts [ (18%nat, mkAF 0x21120 0x21ab0 0); (23%nat, mkAF CW_SB CW_SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition ssH : sstate := mkSS CW_PC_IH sr_atoms [i1h_reg] None i1h_facts.

Lemma cw_EE : forall (regsc : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regsc extra)) n = getr regsc r.
Proof.
intros regsc extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma cw_E32 : forall (regsc : bvmap 5 word) v, ew (Eimg (Ereg regsc [Z_to_bv 64 v])) 32 = Z_to_bv 64 v.
Proof. intros regsc v. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsc _ 0). Qed.

Lemma i1l_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc c nargs,
  getr regsc 23 = w64 CW_SB -> getr regsc 27 = w64 (A_G_REC + 16 + 56 * c + 4) ->
  getr regsc 19 = w64 (CW_SB + (A_G_REC + 16 + 56 * c + 4) / 8) ->
  0 <= c <= 15 -> 0 <= nargs <= 6 ->
  aval_mem (rdW W memc) (A_G_REC + 16 + 56 * c + 4) 4 nargs ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 nargs])) ssL
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_IL)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc c nargs H23 H27 H19 Hc Hn HV.
set (q := A_G_REC + 16 + 56 * c + 4) in *.
assert (Hq : A_G_REC + 20 <= q <= A_G_REC + 20 + 56 * 15) by (subst q; lia).
clearbody q.
assert (HG : A_G_REC = 6174528) by reflexivity.
set (E := Eimg (Ereg regsc [Z_to_bv 64 nargs])).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (cw_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E27 : ew E 27 = Z_to_bv 64 q) by (subst E; rewrite (cw_EE regsc _ 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 nargs) by (subst E; apply cw_E32).
unfold ssL. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_rereg; [subst E; apply regs_ok_Eimg_Ereg | reflexivity |].
  unfold i1_shx27. rewrite (denot_shx E 27 23 0 q CW_SB E27 E23) by (unfold CW_SB; lia).
  rewrite H19. unfold w64. rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, i1l_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E27, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ q 0 4 (SOff 32 0) nargs);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
  rewrite Z.add_0_r. exact (cw_val_of_aval _ _ _ _ _ HV).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok i1l_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E23, E27, E32, !unsigned_lit_small by (unfold CW_SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold CW_SB. repeat split; lia.
Qed.

Lemma i1h_seed : forall (W : world SEGS) (regsc : bvmap 5 word) memc p b,
  getr regsc 23 = w64 CW_SB -> getr regsc 18 = w64 p -> 0x21120 <= p <= 0x21ab0 -> 0 <= b <= 255 ->
  aval_mem (rdW W memc) p 1 b ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 b])) ssH
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_IH)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc p b H23 H18 Hp Hb HV.
set (E := Eimg (Ereg regsc [Z_to_bv 64 b])).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (cw_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E18 : ew E 18 = Z_to_bv 64 p) by (subst E; rewrite (cw_EE regsc _ 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; apply cw_E32).
unfold ssH. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, i1h_reg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E18, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) b);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
  rewrite Z.add_0_r. exact (cw_val_of_aval _ _ _ _ _ HV).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok i1h_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E23, E32, !unsigned_lit_small by (unfold CW_SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold CW_SB. repeat split; lia.
Qed.

Ltac cw_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
Ltac cw_env HS := lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => E
  | st_ok _ ?E _ _ => E
  end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------------- *)
(* the latch IL -> IH (a + 1) | D *)
Lemma seg_I1l : forall c a, ST_IH B MT c (a + 1) -> ST_D B MT c -> ST_IL B MT c a.
Proof.
intros c a HIH HD. unfold ST_IL. intros e lyc Sc Wc regsc memc mdc pos sp1 line j2 Hent HI.
destruct HI as (fn & args & HC & Hj2 & H18 & Hparse).
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & Hiregs & Hcr & Hnth & Ha).
unfold cw_iregs in Hiregs. cbv zeta in Hiregs.
destruct Hiregs as (H19 & H20 & H25 & H26 & H27 & H24).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H23 & _).
pose proof (cw_ent_ncalls B MT e Hent) as Hnc.
pose proof (cw_ent_nargs B MT e _ fn args Hent Hnth) as Hna6.
assert (Hc15 : 0 <= c <= 15) by (unfold cw_ncalls in *; lia).
pose proof (cw_nargs_now e pos lyc Sc Wc memc mdc c fn args Hent HJ ltac:(lia) Hnth) as HNA.
remember (Z.of_nat (length args)) as nargs eqn:Hnargs. try rewrite <- Hnargs in HNA. try rewrite <- Hnargs in Ha.
assert (RA : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 16 + 56 * c + 4) 4).
{ destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 (proj1 HJ) ltac:(left; reflexivity)) as [Z1 _].
  apply (range_addressable_sub _ _ A_G_REC 960); [exact Z1 | lia | lia]. }
pose proof (i1l_seed Wc regsc memc c nargs H23 H27 H19 Hc15 ltac:(lia) HNA) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regsc [Z_to_bv 64 nargs])) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regsc [Z_to_bv 64 nargs])) as HEI.
pose proof (cw_EE regsc [Z_to_bv 64 nargs]) as EV.
pose proof (cw_E32 regsc nargs) as E32.
remember (Eimg (Ereg regsc [Z_to_bv 64 nargs])) as E0 eqn:HE0. clear HE0.
assert (U23 : U E0 (SOff 23 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EV 23%nat 23%bv eq_refl); exact H23 | unfold SHADOW_OFF; lia]).
assert (U27 : U E0 (SOff 27 0) = A_G_REC + 16 + 56 * c + 4)
  by (apply U_atom; [rewrite (EV 27%nat 27%bv eq_refl); exact H27 | unfold A_G_REC; lia]).
unfold cw_at.
(* 0x87c30 .. 0x87c48: the check of nargs, a + 1, the cursors, `blt` *)
paj_run_tok RUN HS HJ SHOK IBspan.
{ cbn [ms_mem]. unfold IBx. rewrite U23, U27. exact RA. }
{ awr_ok_tac. }
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
  pose proof (cw_kept_ro _ rs _ memc m1 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* a + 1 < nargs: back to the head *)
  let E1 := cw_env HS in
  assert (EV1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regsc r) by (cw_EV EV);
  assert (E321 : ew E1 32 = Z_to_bv 64 nargs) by (cw_ew_old; exact E32);
  rewrite (cw_lt_off E1 26 32 1 a nargs (eq_trans (EV1 26%nat 26%bv eq_refl) H26) E321) in Hc by lia.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_IH.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  pmkst HS.
  let E2 := cw_env HS in
  assert (EV2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsc r) by (cw_EV EV).
  cw_preg HS (2%bv : bv 5) P2. cw_preg HS (3%bv : bv 5) P3. cw_preg HS (4%bv : bv 5) P4.
  cw_preg HS (8%bv : bv 5) P8. cw_preg HS (9%bv : bv 5) P9. cw_preg HS (23%bv : bv 5) P23.
  cw_preg HS (18%bv : bv 5) P18. cw_preg HS (19%bv : bv 5) P19. cw_preg HS (20%bv : bv 5) P20.
  cw_preg HS (24%bv : bv 5) P24. cw_preg HS (25%bv : bv 5) P25. cw_preg HS (26%bv : bv 5) P26.
  cw_preg HS (27%bv : bv 5) P27.
  apply (cw_reg_same _ regsc _ 2 2%bv EV2 eq_refl) in P2. apply (cw_reg_same _ regsc _ 3 3%bv EV2 eq_refl) in P3.
  apply (cw_reg_same _ regsc _ 4 4%bv EV2 eq_refl) in P4. apply (cw_reg_same _ regsc _ 8 8%bv EV2 eq_refl) in P8.
  apply (cw_reg_same _ regsc _ 9 9%bv EV2 eq_refl) in P9. apply (cw_reg_same _ regsc _ 23 23%bv EV2 eq_refl) in P23.
  apply (cw_reg_same _ regsc _ 18 18%bv EV2 eq_refl) in P18. apply (cw_reg_same _ regsc _ 24 24%bv EV2 eq_refl) in P24.
  apply (cw_reg_same _ regsc _ 27 27%bv EV2 eq_refl) in P27.
  apply (cw_reg_off _ _ 20 20%bv _ 8 (eq_trans (EV2 20%nat 20%bv eq_refl) H20)) in P20.
  apply (cw_reg_off _ _ 25 25%bv _ 8 (eq_trans (EV2 25%nat 25%bv eq_refl) H25)) in P25.
  apply (cw_reg_off _ _ 26 26%bv _ 1 (eq_trans (EV2 26%nat 26%bv eq_refl) H26)) in P26.
  unfold i1_shx27 in P19.
  rewrite (denot_shx _ 27 23 0 (A_G_REC + 16 + 56 * c + 4) CW_SB (eq_trans (EV2 27%nat 27%bv eq_refl) H27)
    (eq_trans (EV2 23%nat 23%bv eq_refl) H23)) in P19 by (unfold A_G_REC, CW_SB; lia).
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := _ |} _ =>
  assert (HCK : cw_cregs_kept regsc rT) by (repeat split; assumption);
  assert (HMK : cw_mem_kept B (rdW Wc memc) (rdW Wc mT) sp1 (frame_addr (e_ly e) 0 pos))
    by (intros x Hx _ _ _; rewrite K2, K1 by exact Hx; reflexivity);
  destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc rT mT mdv2 pos sp1 line c Hent Hcore Hline Hlscr Hcscr HJ
    HCK HMK) as (Hcore2 & Hline2 & Hlscr2 & Hcscr2);
  assert (HINV : INV_IH B MT e lyc Sc Wc rT mT mdv2 pos sp1 line c (a + 1) j2) end.
  { exists fn, args. split; [|split; [exact Hj2|split; [rewrite P18; exact H18|]]].
    - split; [exact Hcore2|]. split; [exact Hline2|]. split; [exact Hlscr2|]. split; [exact Hcscr2|].
      split; [|split; [exact Hcr|split; [exact Hnth|lia]]].
      unfold cw_iregs. cbv zeta.
      split; [rewrite P19, Z.add_0_r; reflexivity|]. split; [rewrite P20; unfold w64; f_equal; lia|].
      split; [rewrite P25; unfold w64; f_equal; lia|]. split; [rewrite P26; reflexivity|].
      split; [rewrite P27; exact H27|]. rewrite P24; exact H24.
    - replace (Z.to_nat (a + 1)) with (S (Z.to_nat a)) by lia. exact Hparse. }
  exact (HIH e lyc Sc Wc _ _ mdv2 pos sp1 line j2 Hent HINV).
- (* a + 1 >= nargs: on to D *)
  let E1 := cw_env HS in
  assert (EV1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regsc r) by (cw_EV EV);
  assert (E321 : ew E1 32 = Z_to_bv 64 nargs) by (cw_ew_old; exact E32);
  rewrite (cw_lt_off E1 26 32 1 a nargs (eq_trans (EV1 26%nat 26%bv eq_refl) H26) E321) in Hc by lia.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_D.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  pmkst HS.
  let E2 := cw_env HS in
  assert (EV2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsc r) by (cw_EV EV).
  cw_preg HS (2%bv : bv 5) P2. cw_preg HS (3%bv : bv 5) P3. cw_preg HS (4%bv : bv 5) P4.
  cw_preg HS (8%bv : bv 5) P8. cw_preg HS (9%bv : bv 5) P9. cw_preg HS (23%bv : bv 5) P23.
  cw_preg HS (24%bv : bv 5) P24.
  apply (cw_reg_same _ regsc _ 2 2%bv EV2 eq_refl) in P2. apply (cw_reg_same _ regsc _ 3 3%bv EV2 eq_refl) in P3.
  apply (cw_reg_same _ regsc _ 4 4%bv EV2 eq_refl) in P4. apply (cw_reg_same _ regsc _ 8 8%bv EV2 eq_refl) in P8.
  apply (cw_reg_same _ regsc _ 9 9%bv EV2 eq_refl) in P9. apply (cw_reg_same _ regsc _ 23 23%bv EV2 eq_refl) in P23.
  apply (cw_reg_same _ regsc _ 24 24%bv EV2 eq_refl) in P24.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := _ |} _ =>
  assert (HCK : cw_cregs_kept regsc rT) by (repeat split; assumption);
  assert (HMK : cw_mem_kept B (rdW Wc memc) (rdW Wc mT) sp1 (frame_addr (e_ly e) 0 pos))
    by (intros x Hx _ _ _; rewrite K2, K1 by exact Hx; reflexivity);
  destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc rT mT mdv2 pos sp1 line c Hent Hcore Hline Hlscr Hcscr HJ
    HCK HMK) as (Hcore2 & Hline2 & Hlscr2 & Hcscr2);
  assert (HINV : INV_D B MT e lyc Sc Wc rT mT mdv2 pos sp1 line c) end.
  { split; [exact Hcore2|]. split; [exact Hline2|]. split; [exact Hlscr2|]. split; [exact Hcscr2|].
    split; [rewrite P24; exact H24 | exact Hcr]. }
  exact (HD e lyc Sc Wc _ _ mdv2 pos sp1 line Hent HINV).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the head IH -> IK | D *)
Lemma seg_I1h : forall c a, ST_IK B MT c a -> ST_D B MT c -> ST_IH B MT c a.
Proof.
intros c a HIK HD. unfold ST_IH. intros e lyc Sc Wc regsc memc mdc pos sp1 line j Hent HI.
destruct HI as (fn & args & HC & Hj & H18 & Hparse).
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & Hiregs & Hcr & Hnth & Ha).
unfold cw_iregs in Hiregs. cbv zeta in Hiregs.
destruct Hiregs as (H19 & H20 & H25 & H26 & H27 & H24).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _ & H9 & H23 & _).
pose proof Hent as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc memc mdc pos EV_JOINED fn Hent HJ)
  as ([TB TN] & TRA & _ & _ & Tlo & Thi & T8).
remember (bv_unsigned (nth j (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as b eqn:Hbd.
assert (Rb : 0 <= b < 256).
{ pose proof (bv_unsigned_in_range 8 (nth j (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. rewrite Hbd. exact R. }
assert (Hb : aval_mem (rdW Wc memc) (cw_tptr fn + Z.of_nat j) 1 b).
{ intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  rewrite (TB j ltac:(rewrite length_app; cbn [length]; lia)), <- Hbd. f_equal.
  unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !(Z.mod_small b 256) by lia. reflexivity. }
assert (Hb0 : b <> 0 -> (j < length (cw_tpl fn))%nat).
{ intros Hne. destruct (Nat.eq_dec j (length (cw_tpl fn))) as [Heq|Hne']; [|lia]. exfalso. apply Hne. rewrite Hbd.
  rewrite Heq, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
assert (RA0 : range_addressable (rdW Wc memc) SHADOW_OFF (cw_tptr fn + Z.of_nat j) 1)
  by (apply (range_addressable_sub _ _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact TRA | lia | lia]).
pose proof (i1h_seed Wc regsc memc (cw_tptr fn + Z.of_nat j) b H23 H18 ltac:(lia) ltac:(lia) Hb) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regsc [Z_to_bv 64 b])) (mrestrict (w_H Wc) memc))
  by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regsc [Z_to_bv 64 b])) as HEI.
pose proof (cw_EE regsc [Z_to_bv 64 b]) as EV.
pose proof (cw_E32 regsc b) as E32.
remember (Eimg (Ereg regsc [Z_to_bv 64 b])) as E0 eqn:HE0. clear HE0.
assert (U23 : U E0 (SOff 23 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (EV 23%nat 23%bv eq_refl); exact H23 | unfold SHADOW_OFF; lia]).
assert (U18 : U E0 (SOff 18 0) = cw_tptr fn + Z.of_nat j)
  by (apply U_atom; [rewrite (EV 18%nat 18%bv eq_refl); exact H18 | lia]).
unfold cw_at.
(* 0x87b00 .. 0x87b14: the check of the template byte, `beqz` on it *)
paj_run_tok RUN HS HJ SHOK IBspan.
{ cbn [ms_mem]. unfold IBx. rewrite U23, U18. exact RA0. }
{ awr_ok_tac. }
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
  pose proof (cw_kept_ro _ rs _ memc m1 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* the byte is 0: the template is done, on to D *)
  paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_D.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  pmkst HS.
  let E2 := cw_env HS in
  assert (EV2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsc r) by (cw_EV EV).
  cw_preg HS (2%bv : bv 5) P2. cw_preg HS (3%bv : bv 5) P3. cw_preg HS (4%bv : bv 5) P4.
  cw_preg HS (8%bv : bv 5) P8. cw_preg HS (9%bv : bv 5) P9. cw_preg HS (19%bv : bv 5) P19.
  cw_preg HS (20%bv : bv 5) P20. cw_preg HS (23%bv : bv 5) P23. cw_preg HS (24%bv : bv 5) P24.
  cw_preg HS (25%bv : bv 5) P25. cw_preg HS (26%bv : bv 5) P26. cw_preg HS (27%bv : bv 5) P27.
  apply (cw_reg_same _ regsc _ 2 2%bv EV2 eq_refl) in P2. apply (cw_reg_same _ regsc _ 3 3%bv EV2 eq_refl) in P3.
  apply (cw_reg_same _ regsc _ 4 4%bv EV2 eq_refl) in P4. apply (cw_reg_same _ regsc _ 8 8%bv EV2 eq_refl) in P8.
  apply (cw_reg_same _ regsc _ 9 9%bv EV2 eq_refl) in P9. apply (cw_reg_same _ regsc _ 19 19%bv EV2 eq_refl) in P19.
  apply (cw_reg_same _ regsc _ 20 20%bv EV2 eq_refl) in P20. apply (cw_reg_same _ regsc _ 23 23%bv EV2 eq_refl) in P23.
  apply (cw_reg_same _ regsc _ 24 24%bv EV2 eq_refl) in P24. apply (cw_reg_same _ regsc _ 25 25%bv EV2 eq_refl) in P25.
  apply (cw_reg_same _ regsc _ 26 26%bv EV2 eq_refl) in P26. apply (cw_reg_same _ regsc _ 27 27%bv EV2 eq_refl) in P27.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := _ |} _ =>
  assert (HRK : cw_regs_kept regsc rT) by (repeat split; assumption);
  assert (HMK : cw_mem_kept B (rdW Wc memc) (rdW Wc mT) sp1 (frame_addr (e_ly e) 0 pos))
    by (intros x Hx _ _ _; rewrite K2, K1 by exact Hx; reflexivity);
  pose proof (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc rT mT mdv2 pos sp1 line c a fn args Hent HC HJ
    HRK HMK) as HC2 end.
  destruct HC2 as (Hcore2 & Hline2 & Hlscr2 & Hcscr2 & _).
  exact (HD e lyc Sc Wc _ _ mdv2 pos sp1 line Hent
    (conj Hcore2 (conj Hline2 (conj Hlscr2 (conj Hcscr2 (conj (eq_trans P24 H24) Hcr)))))).
- (* the byte is not 0: strspn(s2, " ") *)
  let E1 := cw_env HS in
  assert (E321 : ew E1 32 = Z_to_bv 64 b) by (cw_ew_old; exact E32);
  rewrite (cw_eq0_lit E1 32 b E321 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc. pose proof (Hb0 Hc) as Hjl.
  (* 0x87b18 .. 0x87b20: a0 = s2, a1 = " ", the call *)
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  let E2 := cw_env HS in
  assert (EV2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsc r) by (cw_EV EV).
  cw_preg HS (10%bv : bv 5) Ra0. cw_preg HS (11%bv : bv 5) Ra1. cw_preg HS (1%bv : bv 5) Rra.
  cw_preg HS (2%bv : bv 5) P2. cw_preg HS (3%bv : bv 5) P3. cw_preg HS (4%bv : bv 5) P4.
  apply (cw_reg_off _ _ 18 10%bv _ 0 (eq_trans (EV2 18%nat 18%bv eq_refl) H18)) in Ra0. rewrite Z.add_0_r in Ra0.
  apply (cw_reg_off _ _ 24 11%bv _ 0 (eq_trans (EV2 24%nat 24%bv eq_refl) H24)) in Ra1. rewrite Z.add_0_r in Ra1.
  apply (cw_reg_same _ regsc _ 2 2%bv EV2 eq_refl) in P2. apply (cw_reg_same _ regsc _ 3 3%bv EV2 eq_refl) in P3.
  apply (cw_reg_same _ regsc _ 4 4%bv EV2 eq_refl) in P4.
  let E2 := cw_env HS in
  lazymatch goal with HEI2 : img_env _ _ E2 |- _ =>
    change (SOff 240 5696) with (SOff A_TEXT 5696) in Rra; rewrite (codeptr_val E2 5696 HEI2) in Rra end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := _ |} _ =>
    destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mT mdv2 pos EV_JOINED fn Hent HJ)
      as ([TB2 TN2] & TRA2 & THV2 & TTL2 & _);
    destruct (cw_sp1_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mT mdv2 pos EV_JOINED Hent HJ)
      as (SP2 & SRA2 & SHV2 & STL2);
    pose proof (cw_arodata_now e pos lyc Sc Wc mT mdv2 EV_JOINED Hent HJ) as HROD2;
    assert (HspT : spZ rT = sp1) by (unfold spZ; rewrite P2; exact Hsp) end.
  eapply SRr_bind.
  { apply (aj_strspn_at B LAWS TL cmd_rec_cells _ ASTRSPN Wc _ _ CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e)
      (e_W e) (e_mem e) (e_md e) [(0, pos)] lyc Sc mdv2 EV_JOINED (cw_tptr fn + Z.of_nat j) 0x21120
      (skipn j (cw_tpl fn)) CW_SP1 (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + 5696)) HJ Ra0 Ra1).
    - lia.
    - lia.
    - rewrite HspT. lia.
    - apply cw_o16; [exact Hsp32 | exact Hal16].
    - lia.
    - rewrite Hes, WS. lia.
    - rewrite P3, G3. exact Hgp.
    - rewrite P4, G4. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (astr_atR_view SEGS). exact (astr_atR_skipn _ _ _ j (conj TB2 TN2) ltac:(lia)).
    - apply (astr_atR_view SEGS). exact SP2.
    - unfold aread_ok, astr_len. rewrite length_skipn.
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros x Hx. split.
        - replace x with (cw_tptr fn + Z.of_nat (Z.to_nat (x - cw_tptr fn))) by lia.
          rewrite (TB2 (Z.to_nat (x - cw_tptr fn))) by (rewrite length_app; cbn [length]; lia). discriminate.
        - unfold ascratch_stk. rewrite HspT. lia. }
      split; [unfold amem_range; left; rewrite C5; lia|].
      split; [apply (range_addressable_sub _ _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact TRA2 | lia | lia]|].
      intros _. apply (cw_hull_sub _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact THV2 | lia | lia | lia].
    - (* the item's band (+ 8): a g_call_words literal in .rodata, low band (band-premise survey, call site 5) *)
      unfold amem_range, astr_len. rewrite length_skipn. left. rewrite C5. lia.
    - change (astr_len CW_SP1 + 1) with 2. destruct SP2 as [SB2 _]. unfold aread_ok.
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros x Hx. split.
        - replace x with (0x21120 + Z.of_nat (Z.to_nat (x - 0x21120))) by lia.
          rewrite (SB2 (Z.to_nat (x - 0x21120))) by (cbn [length app CW_SP1]; lia). discriminate.
        - unfold ascratch_stk. rewrite HspT. lia. }
      split; [unfold amem_range; left; rewrite C5; lia|]. split; [exact SRA2|]. intros _. exact SHV2.
    - (* the set " " at 0x21120, .rodata, low band *)
      change (astr_len CW_SP1 + 8) with 9. unfold amem_range. left. rewrite C5. lia.
    - unfold astr_len. rewrite length_skipn.
      replace (cw_tptr fn + Z.of_nat j + Z.of_nat (length (cw_tpl fn) - j))
        with (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) by lia.
      exact TTL2.
    - change (0x21120 + astr_len CW_SP1) with 0x21121. exact STL2.
    - apply cmd_rom_view_on. exact HROD2. }
  (* back at 0x87b24: s2 += the answer, the check of the byte at the new s2 *)
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hspn & Hfr2).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H Wc) mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS2.
  remember (PSpn.spn_len CW_SP1 (skipn j (cw_tpl fn))) as spn eqn:Hspd. try rewrite <- Hspd in Hspn.
  assert (Hspn8 : (spn <= length (cw_tpl fn) - j)%nat)
    by (pose proof (cw_spn_le CW_SP1 (skipn j (cw_tpl fn))) as L; rewrite length_skipn in L; rewrite Hspd; exact L).
  lazymatch type of HS2 with st_ok_pi _ _ (havoc ?E2 ?k ?ws) _ _ =>
    lazymatch goal with HEI2 : img_env _ _ E2 |- _ =>
      pose proof (img_env_havoc E2 k ws HEI2 ltac:(cbv; lia)) as HEI3 end;
    assert (E344 : ew (havoc E2 k ws) 44 = getr regs2 10) by reflexivity;
    assert (EV3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (havoc E2 k ws) n = getr regsc r)
      by (cw_EV EV);
    remember (havoc E2 k ws) as E3 eqn:HE3 end.
  clear HE3 HS SHOK.
  assert (Hfact : afact_ok E3 44 (mkAF 0 8 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E344, Hspn. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
  pose proof (st_ok_pi_add_fact E3 _ _ 44 (mkAF 0 8 0) HS2 Hfact) as HS. clear HS2.
  assert (SHOK : sh_ok SEGS IBx [] E3 (mrestrict (w_H Wc) mem2)) by (unfold sh_ok; apply Forall_nil).
  assert (U23' : U E3 (SOff 23 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (EV3 23%nat 23%bv eq_refl); exact H23 | unfold SHADOW_OFF; lia]).
  assert (U18' : U E3 (SOff 18 0) = cw_tptr fn + Z.of_nat j)
    by (apply U_atom; [rewrite (EV3 18%nat 18%bv eq_refl); exact H18 | lia]).
  assert (U44 : U E3 (SOff 44 0) = Z.of_nat spn) by (apply U_atom; [rewrite E344; exact Hspn | lia]).
  clear HJ.
  paj_run_to_tok RUNTO HS HJ2 SHOK IBspan CW_PC_IK.
  { cbn [ms_mem]. unfold IBx. rewrite U23', (cw_U_add E3 _ _ _ _ U18' U44) by lia.
    destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem2 md2 pos EV_JOINED fn Hent HJ2)
      as (_ & TRA3 & _).
    apply (range_addressable_sub _ _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact TRA3 | lia | lia]. }
  { awr_ok_tac. }
  set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (cw_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
  clear HF HFr HG.
  pmkst HS.
  let E4 := cw_env HS in
  assert (EV4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regsc r) by (cw_EV EV3);
  assert (U18'' : U E4 (SOff 18 0) = cw_tptr fn + Z.of_nat j)
    by (apply U_atom; [rewrite (EV4 18%nat 18%bv eq_refl); exact H18 | lia]);
  assert (U44' : U E4 (SOff 44 0) = Z.of_nat spn)
    by (apply U_atom; [cw_ew_old; rewrite E344; exact Hspn | lia]).
  cw_preg HS (2%bv : bv 5) Q2. cw_preg HS (3%bv : bv 5) Q3. cw_preg HS (4%bv : bv 5) Q4.
  cw_preg HS (8%bv : bv 5) Q8. cw_preg HS (9%bv : bv 5) Q9. cw_preg HS (19%bv : bv 5) Q19.
  cw_preg HS (20%bv : bv 5) Q20. cw_preg HS (23%bv : bv 5) Q23. cw_preg HS (24%bv : bv 5) Q24.
  cw_preg HS (25%bv : bv 5) Q25. cw_preg HS (26%bv : bv 5) Q26. cw_preg HS (27%bv : bv 5) Q27.
  cw_preg HS (18%bv : bv 5) Q18.
  apply (cw_reg_same _ regsc _ 2 2%bv EV4 eq_refl) in Q2. apply (cw_reg_same _ regsc _ 3 3%bv EV4 eq_refl) in Q3.
  apply (cw_reg_same _ regsc _ 4 4%bv EV4 eq_refl) in Q4. apply (cw_reg_same _ regsc _ 8 8%bv EV4 eq_refl) in Q8.
  apply (cw_reg_same _ regsc _ 9 9%bv EV4 eq_refl) in Q9. apply (cw_reg_same _ regsc _ 19 19%bv EV4 eq_refl) in Q19.
  apply (cw_reg_same _ regsc _ 20 20%bv EV4 eq_refl) in Q20. apply (cw_reg_same _ regsc _ 23 23%bv EV4 eq_refl) in Q23.
  apply (cw_reg_same _ regsc _ 24 24%bv EV4 eq_refl) in Q24. apply (cw_reg_same _ regsc _ 25 25%bv EV4 eq_refl) in Q25.
  apply (cw_reg_same _ regsc _ 26 26%bv EV4 eq_refl) in Q26. apply (cw_reg_same _ regsc _ 27 27%bv EV4 eq_refl) in Q27.
  rewrite denot_lit_U, (cw_U_add _ _ _ _ _ U18'' U44') in Q18 by lia.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := _ |} _ =>
  assert (HRK : cw_regs_kept regsc rT) by (repeat split; assumption);
  assert (HMK : cw_mem_kept B (rdW Wc memc) (rdW Wc mT) sp1 (frame_addr (e_ly e) 0 pos));
  [ intros x Hx Hw _ _; rewrite K3 by exact Hx;
    rewrite (Hfr2 x Hx) by first [exact (fun f : False => f) | lia];
    rewrite K2, K1 by exact Hx; reflexivity
  | ];
  pose proof (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regsc memc mdc rT mT mdv3 pos sp1 line c a fn args Hent HC HJ2
    HRK HMK) as HC2;
  assert (HINV : INV_IK B MT e lyc Sc Wc rT mT mdv3 pos sp1 line c a (j + spn)%nat) end.
  { exists fn, args. split; [exact HC2|]. split; [lia|]. split.
    - rewrite Q18. unfold w64. f_equal. lia.
    - rewrite (cw_parse_step (skipn j (cw_tpl fn))) in Hparse.
      + assert (EK : skipn (PSpn.spn_len CW_SP1 (skipn j (cw_tpl fn))) (skipn j (cw_tpl fn)) = skipn (j + spn) (cw_tpl fn))
          by (rewrite skipn_skipn; f_equal; rewrite Hspd; lia).
        rewrite EK in Hparse. exact Hparse.
      + intros Hnil. apply (f_equal (@length byte)) in Hnil. rewrite length_skipn in Hnil. cbn [length] in Hnil. lia. }
  exact (HIK e lyc Sc Wc _ _ mdv3 pos sp1 line (j + spn)%nat Hent HINV).
Qed.

End e.
End f.
End d.
