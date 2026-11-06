(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v (x2_realizes, :184) for plugin-hostd/fuzz_command's ASan image: module paths changed, TfibSyms -> CmdBSyms, addresses moved to fuzz_command.asan; the descriptor table the walk reads, the shadow windows it clears and the shadow-byte check are computed from the image's 180 asan_globals descriptors (RtDtorTbl.v), as omx-clap-core/fuzz_preset's lib/A/AE37.v computes them for its 57; write windows added for the four ODR indicator bytes __asan_unregister_globals clears; the theorem (cmd_x2_realizes) is the statement of the class DtorExit (lib/A/AE37.v:14), closed as the instance cmd_dtor_exit. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDtorExit.v (donor image sha256 c0661b96b5bd), with its module paths changed, names CmdBSyms -> SegBSyms and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtDtorExit.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YE34 YF0l YF0m YE3g YE2p YE3i YE3h YE3m YE23 YF0x YE20 YE2y YE7f YE37.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDtorTbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition A_GLOBALS_REGISTERED : Z := 0xa9100.   (* symbol ___asan_globals_registered (8 bytes) *)
Definition A_MU_FOR_GLOBALS : Z := 0xaa070.   (* __asan::mu_for_globals: allow_after_dynamic_init 0xae930 + 64 (0x42b04, 0x42b1c) *)
(* the seven words of a record at table offset o that the walk reads (it does not read the name pointer at o + 24) *)
Definition x2_rec_cells (o : Z) (g : aglobal) : list (Z * N * Z) :=
[(o, 8%N, g_beg g); (o + 8, 8%N, g_size g); (o + 16, 8%N, g_srz g); (o + 32, 8%N, g_module g);
(o + 40, 8%N, g_dyn g); (o + 48, 8%N, g_loc g); (o + 56, 8%N, g_odr g)].
Fixpoint x2_desc_from (o : Z) (gs : list aglobal) : list (Z * N * Z) :=
match gs with [] => [] | g :: t => x2_rec_cells o g ++ x2_desc_from (o + 64) t end.
Definition x2_desc : list (Z * N * Z) := x2_desc_from 0 x2_globals.
(* the shadow bytes the walk sets to 0: those of each global with its guard bytes, and those of the descriptor table *)
Definition x2_gwin (g : aglobal) : Z * Z := (shadow_of_addr SHADOW_OFF (g_beg g), g_srz g / 8).
Definition x2_gwins : list (Z * Z) :=
map x2_gwin x2_globals ++ [(shadow_of_addr SHADOW_OFF A_ASAN_GLOBALS, A_ASAN_GLOBALS_SZ / 8)].
Fixpoint win_ins (w : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
match l with [] => [w] | v :: t => if fst w <=? fst v then w :: l else v :: win_ins w t end.
Definition win_cons (w : Z * Z) (acc : list (Z * Z)) : list (Z * Z) :=
match acc with v :: t => if fst w + snd w =? fst v then (fst w, snd w + snd v) :: t else w :: acc | [] => [w] end.
(* the same windows sorted by address, adjacent ones merged *)
Definition x2_shw : list (Z * Z) := Eval vm_compute in fold_right win_cons [] (fold_right win_ins [] x2_gwins).
(* the odr indicator bytes (g_odr of 4 records, RtDtorTbl.v) that the walk sets to 0 (0x42d10 sb zero,0(a0)) *)
Definition x2_odr : list (Z * Z) := [(0x5deee0, 1)].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation tbl2 := tbl_x213 (only parsing).
Notation tbl2_ok := tbl_x213_ok (only parsing).
(* the words the walk reads besides the descriptors: the constant at 0x103a8 (0x42ea0); the GOT slots 0xa63d0..0xa6410
   (0x42bf4..0x42c18: page-size cache, common_flags, flags, shadow offset, kMidMemBeg/End, kHighMemEnd, REAL(memset));
   the start/stop pair at 0xa7088 (0x89150, 0x89154); the REAL(memset) slot 0xa82b0 -> memset 0x9ef40; flags()
   report_globals (0xae8b8 + 24) and the word holding byte 78; can_poison_memory 0xb091c (0x59814); the shadow offset
   0xb10b8; asan_inited 0xb1d98 (0x5e734); kHighMemEnd, kMidMemBeg, kMidMemEnd at 0xb1da0; the page size 0x140b60;
   common_flags()->clear_shadow_mmap_threshold 0x142be8 + 120 *)
Definition x2_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0x103a0, 8, [(0, 8%N, 0xafffff00000fffff)]);
(0xa31f0, 72, [(0, 8%N, 0x13c260); (8, 8%N, 0xa50e0); (16, 8%N, 0x13e2e8); (24, 8%N, 0xa9fb8); (32, 8%N, 0xac7b8);
(40, 8%N, 0xad4a8); (48, 8%N, 0xad4b0); (56, 8%N, 0xad4a0); (64, 8%N, 0xa50a8)]);
(0xa3e88, 16, [(0, 8%N, A_ASAN_GLOBALS); (8, 8%N, A_ASAN_GLOBALS + A_ASAN_GLOBALS_SZ)]);
(0xa50a8, 8, [(0, 8%N, 0x9afd4)]);
(A_ASAN_GLOBALS, A_ASAN_GLOBALS_SZ, x2_desc);
(0xa9fd0, 8, [(0, 8%N, 0x101010000000001)]);
(0xaa000, 8, [(0, 8%N, 0x1000100000000)]);
(0xac01c, 1, [(0, 1%N, 1)]);
(0xac7b8, 8, [(0, 8%N, 0x7fff8000)]);
(0xad498, 1, [(0, 1%N, 1)]);
(0xad4a0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x13c260, 8, [(0, 8%N, 0x1000)]);
(0x13e360, 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition shw_region (w : Z * Z) : YP09.region :=
YP09.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions : smem :=
YP09.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr A_GLOBALS_REGISTERED 8 (SLit 1) true
:: cellr A_MU_FOR_GLOBALS 8 (SLit 0) true
:: map shw_region x2_odr ++ map shw_region x2_shw ++ map ro_region x2_rodata.
Definition ss_x2 : sstate := mkSS X2_PC sr_atoms x2_regions None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x2_st : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl2 FUEL ss_x2).
Lemma x2_run : sym_runN tfibsegs tbl2 FUEL ss_x2 = (x2_st, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma x2_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl2 FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl2 tbl2_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition const_chk (ly : alayout) (a : Z) (n : N) (v : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') w' (AV (ANum v'))) => (a' =? a) && Nat.eqb w' (N.to_nat n) && (v' =? v)
| _ => false
end.
Lemma const_chk_sound : forall ly a n v, const_chk ly a n v = true ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) (N.to_nat n) (AV (ANum v))).
Proof.
intros ly a n v H. unfold const_chk in H.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|]; [|discriminate].
destruct e; try discriminate. destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition rodata_chk (ly : alayout) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r))
x2_rodata.
Lemma rodata_chk_true : forall ly, rodata_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S k => lo :: zrange (lo + 1) k end.
Lemma In_zrange : forall n lo a, lo <= a < lo + Z.of_nat n -> In a (zrange lo n).
Proof.
induction n as [|n IH]; intros lo a Ha; [lia|]. cbn [zrange].
destruct (Z.eq_dec a lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.
(* every byte of every shadow window, and the check that each is a 1-byte cell of Tfib_const or lies in the shadow of
   a range of Tfib_zero_shadow *)
Definition x2_wbytes : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw.
Definition cbyte_chk (ly : alayout) (a : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end.
Definition zbyte_chk (a : Z) : bool :=
existsb (fun r => (shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8))
Tfib_zero_shadow.
Definition wbyte_chk (ly : alayout) : bool := forallb (fun a => cbyte_chk ly a || zbyte_chk a) x2_wbytes.
Lemma wbyte_chk_true : forall ly, wbyte_chk ly = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition shw_bounds : bool :=
forallb (fun w => (0 <=? fst w) && (TFIB_IMG_END <=? fst w) && (0 <=? snd w) && (fst w + snd w <=? 2 ^ 47)) x2_shw.
Lemma shw_bounds_true : shw_bounds = true.
Proof. vm_compute. reflexivity. Qed.
(* the odr indicator windows lie in a writable segment of the image *)
Definition odr_chk : bool :=
forallb (fun w => (0 <=? fst w) && (0 <=? snd w) && (fst w + snd w <=? 2 ^ 47) &&
wseg_ok tfibsegs (Z_to_bv 64 (fst w)) (Z.to_nat (snd w))) x2_odr.
Lemma odr_chk_true : odr_chk = true.
Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis TB : SegBSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfib_const ly) (ANum 0xaa070) = Some (ACell (ANum 0xaa070) 8 (AV (ANum 0))).
Lemma rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region x2_rodata).
Proof.
intros ly S H mem E HM. pose proof (rodata_chk_true ly) as Hc. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
apply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma cbyte_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> cbyte_chk ly a = true -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hc. unfold cbyte_chk in Hc.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|discriminate].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. subst.
pose proof (tfib_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. eexists. exact Hv.
Qed.
Lemma zbyte_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfibsegs H mem) -> zbyte_chk a = true -> exists b, mbyte tfibsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hc. unfold zbyte_chk in Hc. apply existsb_exists in Hc as ([lo n] & Hin & Hc).
cbn [fst snd] in Hc. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) (lo, n)
ltac:(unfold zero_shadow_ranges; right; rewrite (ts_zsh _ TB); exact Hin)) as HZ.
specialize (HZ (a - shadow_of_addr SHADOW_OFF lo) ltac:(cbn [fst snd]; lia)). cbn [fst snd] in HZ.
replace (shadow_of_addr SHADOW_OFF lo + (a - shadow_of_addr SHADOW_OFF lo)) with a in HZ by lia.
unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. pose proof (wbyte_chk_true ly) as Hc. unfold wbyte_chk in Hc. rewrite forallb_forall in Hc.
pose proof shw_bounds_true as Hb. unfold shw_bounds in Hb. rewrite forallb_forall in Hb.
apply Forall_map. apply Forall_forall. intros [lo n] Hin.
specialize (Hb _ Hin). cbn [fst snd] in Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [Hb H2].
apply andb_prop in Hb as [H0 H1].
apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
assert (Hbo : exists b, mbyte tfibsegs (mrestrict H mem) o = Some b).
{ assert (Hw : In o x2_wbytes).
{ unfold x2_wbytes. apply in_flat_map. exists (lo, n). split; [exact Hin|]. cbn [fst snd].
apply In_zrange. rewrite Z2Nat.id by lia. lia. }
specialize (Hc o Hw). apply orb_prop in Hc as [Hc|Hc];
[exact (cbyte_present ly S H mem o HM Hc) | exact (zbyte_present ly S H mem o HM Hc)]. }
destruct Hbo as [b Hbo].
apply (mbyte_high_writable _ o b); [lia | exact Hbo].
Qed.
Lemma odr_ok : forall (m : word -> option byte) E,
Forall (region_ok tfibsegs E m) (map shw_region x2_odr).
Proof.
intros m E. pose proof odr_chk_true as Hc. unfold odr_chk in Hc. rewrite forallb_forall in Hc.
apply Forall_map. apply Forall_forall. intros [lo n] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [Hc H2].
apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.
exact (wseg_writable m lo n o Hz H0 H2 H1 ltac:(lia)).
Qed.
Lemma zi8_flag : wseg_ok tfibsegs (Z_to_bv 64 A_GLOBALS_REGISTERED) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma zi8_mu : wseg_ok tfibsegs (Z_to_bv 64 A_MU_FOR_GLOBALS) (Z.to_nat 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
vm_compute in Ht. unfold XW2. unfold X2_STK in *.
repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia|]). destruct Ht.
Qed.
Theorem cmd_x2_realizes : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 HAR) as HM.
unfold cfg_at. change (w64 X2_PC) with (Z_to_bv 64 X2_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (E := Ereg regs (@nil word)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (HS0 : st_ok tfibsegs E ss_x2 (restrict (w_H W) (mkst regs (Z_to_bv 64 X2_PC) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x2. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold x2_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split; [exact (odr_ok _ E) | apply Forall_app; split; [exact (shw_ok ly S _ mem E HM) | exact (rodata_ok ly S _ mem E HM)]]]]].
+ apply (region_ok_stack tfibsegs E _ 2 sp0 (- X2_STK)); [exact E2 | unfold X2_STK; lia | lia |].
intros a Ha. apply YE2y.apresent_writable. apply HpresE. unfold X2_STK in Ha. lia.
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
unfold A_GLOBALS_REGISTERED.
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xa9100 8); [exact zi8_flag | lia | lia | lia | lia] |].
constructor; [|constructor]. apply (chunk_ok_val tfibsegs E _ 0 0xa9100 8 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xa9100 8 1 HM ltac:(vm_compute; reflexivity)).
+ unfold region_ok, cellr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val Z.of_N].
unfold A_MU_FOR_GLOBALS.
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; apply (wseg_writable _ 0xaa070 8); [exact zi8_mu | lia | lia | lia | lia] |].
constructor; [|constructor]. apply (chunk_ok_val tfibsegs E _ 0 0xaa070 8 (SLit 0) 0); [reflexivity | zside | zside |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S _ mem 0xaa070 8 0 HM (MU0 ly)).
- apply pairwise_disjoint_of_extents. unfold x2_regions, x2_odr, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
unfold X2_STK, A_GLOBALS_REGISTERED, A_MU_FOR_GLOBALS, A_ASAN_GLOBALS, A_ASAN_GLOBALS_SZ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; lia. }
eapply SRr_bind; [apply (x2_phase W E ss_x2 x2_st _ _ md HS0 x2_run)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfibsegs tbl2 tbl2_ok Hwx W E); [exact HS1 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) -> ms_mem ms1 x = mem x).
{ intros x Hx. apply HF1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (MEQr : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) ->
mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr1. intros Hin. apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [left; exact Hw | right; exact Hw]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X2_STK <= a < sp0) -> ~ XW2 a ->
aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply MEQr. rewrite unsigned_lit_small by lia. tauto. }
assert (PRS : forall a, sp0 - X2_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. unfold X2_STK in Ha. apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite E2 in Hw. unfold X2_STK in Hw.
replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia. }
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (symmetry; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [reflexivity|].
split; [|split; [|split]].
- exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity]) ltac:(vm_compute; reflexivity)).
- apply with_vm_backing_same.
- intros a Hr Hs Hx. apply AV; [exact Hr | unfold X2_STK; unfold sp0 in *; lia | exact Hx].
- intros a Hr Hx Hp.
destruct (Z_lt_le_dec a (sp0 - X2_STK)) as [L1|L1]; [| destruct (Z_lt_le_dec a sp0) as [L2|L2]; [apply PRS; lia|]].
all: destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite MEQ; [exact Hb|]; rewrite unsigned_lit_small by lia; intros [Hw|Hw]; [lia | exact (Hx Hw)].
Qed.
End S.
End d.
(* the class DtorExit (lib/A/AE37.v:14-16), discharged *)
Instance cmd_dtor_exit : DtorExit.
Proof. intros fx rc B TB MU0. exact (@cmd_x2_realizes fx rc B TB MU0). Qed.
