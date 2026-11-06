(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file's
   walk, its third piece: MID2 (0x88134) -> DONE (0x89114, the empty text) or HEAD (0x881f8, the first line).
   The B3 segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment walk lib/A/Prog/pf_a2.v
   (commit 3f59c8d75ed4: seed, plain runs, region read-back), re-derived on image B's code:
     0x88134 srli a0,s11,3; add a0,a0,s4; lb a0,0(a0); 0x88140 beqz a0 -> 0x88148    inline check B#2 (load1 of *p;
             the shadow byte s of t's granule; s = 0, or s <> 0 and the cold slow path 0x891e4 `andi a1,s11,7;
             bge a1,a0` -> error path 0x891f0 is not taken (t mod 8 < s: reader_pre's sa_addr t (|s| + 1),
             saddr_ok), `j 0x88148`)
     0x88148 lbu a0,0(s11); sd s3,88(s1); srli a1,s3,3; sd a1,80(s1); 0x88158 bnez a0 -> 0x88160, else
             0x8815c j DONE 0x89114
     0x88160 .. 0x881f4 the setup: s8 = 0, slot 0xc0 = NULL, the 19 slots of PF_SL the loop reads (F + 0x40 ..
             F + 0x450, ~c, c + 0x160, c + 0x34d0, .str.2 / .str.3, 0x2c80, ~buf / ~model low / ~low), s2 = '#',
             s10 = -1; HEAD 0x881f8.
   The check is not the token executor's (its slow block lies out of line, YCbn slow_block expects it at the
   fall-through): a plain run reads the shadow byte through an alias ((s11 >> 3) + s4 = the cell's atom) and the two
   branches are split by hand; the error arm is refuted by pb3_trap_b2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B3_f pf_seg_B3_t pf_seg_B3_k pf_seg_B3_p1 pf_seg_B3_p2.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a YO0b YO0c YI08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pb3_le_byte1 : forall s, 0 <= s < 256 -> le_byte s 1 0 = s.
Proof.
intros s Hs. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
(* the slow path's `bge a1,a0` (a1 = t & 7, a0 = the shadow byte s <> 0) is taken only when t mod 8 >= s, which
   saddr_ok t s excludes *)
Lemma pb3_trap_b2 : forall E t s,
  ew E 27 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 -> ew E 33 = Z_to_bv 64 s -> saddr_ok t s -> s <> 0 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff 27 0) (SLit 7))) (sv_denot E (SOff 33 0)) = true -> False.
Proof.
intros E t s E27 Ht E33 Hok Hs0 Hc.
destruct Hok as [-> | [H1 H2]]; [exact (Hs0 eq_refl)|].
rewrite branch_ge in Hc.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff 27 0) (SLit 7)))) with (U E (SAlu ALU_AND (SOff 27 0) (SLit 7))) in Hc.
change (bv_unsigned (sv_denot E (SOff 33 0))) with (U E (SOff 33 0)) in Hc.
rewrite U_and_lit in Hc by lia. rewrite (U_atom E 27 t E27 Ht), (U_atom E 33 s E33) in Hc by lia.
change 7 with (Z.ones 3) in Hc. rewrite Z.land_ones in Hc by lia. change (2 ^ 3) with 8 in Hc.
pose proof (Z.mod_pos_bound t 8 ltac:(lia)).
rewrite (s64_small (t mod 8)), (s64_small s) in Hc by lia. apply Bool.negb_true_iff, Z.ltb_ge in Hc. lia.
Qed.
(* the 64-bit `not` of an atom plus an offset *)
Lemma pb3_den_not : forall E n x k, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n k) (SLit (-1))) = Z_to_bv 64 (pf_nt (x + k)).
Proof.
intros E n x k Hn Hx Hk. change (Z_to_bv 64 (pf_nt (x + k))) with (sv_denot E (SLit (pf_nt (x + k)))).
apply U_inj. rewrite (U_not_off E n x k Hn Hx Hk). unfold pf_nt. rewrite U_lit by lia. reflexivity.
Qed.
Lemma pb3_den_srl3 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = Z_to_bv 64 (x / 8).
Proof.
intros E n x Hn Hx. change (Z_to_bv 64 (x / 8)) with (sv_denot E (SLit (x / 8))).
apply U_inj. rewrite U_srl3, (U_atom E n x Hn Hx).
assert (0 <= x / 8 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite U_lit by lia. reflexivity.
Qed.

(* ---------- the check B#2 (0x88134 .. 0x88148) ---------- *)
(* every register its own atom; atom 32 = t's shadow cell, atom 33 = its byte s; the alias (s11 >> 3) + s4 = atom
   32; the region: the cell, read-only *)
Definition pb3_shx3 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0) (SLit 3)) (SOff 20 0).
Definition pb3_ss3a : sstate := mkSS (AF_reac_segconf_parse_file + 0x2fc) sr_atoms
  [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
  (mkFacts [(33%nat, mkAF 0 7 0)] [] [(pb3_shx3, SOff 32 0)]).
(* ---------- from 0x88148 to DONE / HEAD ---------- *)
(* every register its own atom but s2 = 0x3000 (pinned); atoms 32 = F, 33 = c, 34 = sh(c + 0x40e0), 35 = t[0];
   the regions: the slots s1 + 0x00 .. 0xd8 (the slots MID2 knows as chunks; read-only in the seed, made writable
   before the run), t's first byte *)
Definition pb3_r3s1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x00 0xd8 0x00 0x00
  [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x98 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x18 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 33 0x40e0));
   YP09.mkChunk 0x40 (CVal 8 (SOff 32 0x20)); YP09.mkChunk 0x48 (CVal 8 (SOff 33 0x4080))].
Definition pb3_r3t : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition pb3_ss3b0 : sstate := mkSS (AF_reac_segconf_parse_file + 0x310) sr_atoms [pb3_r3s1; pb3_r3t] None
  (mkFacts [(35%nat, mkAF 0 255 0)] [] []).
Definition pb3_ss3b : sstate := mkSS (AF_reac_segconf_parse_file + 0x310) (sr_set sr_atoms (Z_to_bv 5 18) (SLit 0x3000))
  [pb3_r3s1; pb3_r3t] None (mkFacts [(35%nat, mkAF 0 255 0)] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma pb3_obj36 : forall E, img_env VAL A_LIM E -> ew E 277%nat = w64 (seg_litA_rc [SP; TAB; CR]).
Proof.
intros E HE. rewrite (img_env_atomP E 277%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 277%nat with (A_OBJ 36). rewrite (OBJ 36%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma pb3_obj37 : forall E, img_env VAL A_LIM E -> ew E 278%nat = w64 (seg_litA_rc F_long).
Proof.
intros E HE. rewrite (img_env_atomP E 278%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 278%nat with (A_OBJ 37). rewrite (OBJ 37%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma pb3_seed3a : forall (Wc : world SEGS) (rX : bvmap 5 word) memc t s,
  getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 27) = w64 t -> 0 <= t < 2 ^ 47 ->
  rdW Wc memc (SHADOW_OFF + t / 8) = Some s -> 0 <= s <= 7 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (SHADOW_OFF + t / 8); w64 s])) pb3_ss3a
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x2fc))) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc t s R20 R27 Ht Hs Hs7.
set (E := Eimg (Ereg rX [w64 (SHADOW_OFF + t / 8); w64 s])).
assert (Htq : 0 <= t / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E27 : ew E 27 = w64 t) by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 27 (Z_to_bv 5 27) eq_refl); exact R27).
assert (E32 : ew E 32 = w64 (SHADOW_OFF + t / 8)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + t / 8)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = s) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U32. unfold SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (SHADOW_OFF + t / 8) 0 1 (SOff 33 0) s).
  + rewrite pb3_den_atom0, E33. reflexivity.
  + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  + cbn. lia.
  + change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r. apply pb3_val_mem_of_sa_val.
    intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, pb3_le_byte1 by lia. exact Hs.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, Z.pow_0_r, Z.mod_1_r. lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. unfold pb3_shx3. apply U_inj.
    rewrite U_SAlu, U_srl3.
    rewrite (U_atom E 27 t E27) by lia. rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 32 (SHADOW_OFF + t / 8) E32) by (unfold SHADOW_OFF; lia).
    cbn [zalu_raw]. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* readers that agree on every address keep the record, the slots, the cells *)
Lemma pb3_same_rconf : forall (rd rd' : reader) c cf, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  0 <= c -> c + seg_spec.SEG_C_SIZE <= 2 ^ 64 -> sa_rconf rd c cf -> sa_rconf rd' c cf.
Proof.
intros rd rd' c cf HK H0 H1 (bs & Hb & Henc). exists bs. split; [|exact Henc].
pose proof Henc as (HL & _). intros i Hi. rewrite HK; [exact (Hb i Hi)|].
unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma pb3_same_sl : forall (rd rd' : reader) b L, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  (forall o x, In (o, x) L -> 0 <= b + o /\ b + o + 8 <= 2 ^ 64) -> pf_sl rd b L -> pf_sl rd' b L.
Proof.
intros rd rd' b L HK HB H. unfold pf_sl in *. rewrite Forall_forall in *. intros [o x] Hin.
cbn [fst snd]. specialize (H (o, x) Hin). cbn [fst snd] in H. destruct (HB o x Hin) as [B0 B1].
rewrite (rdword_ext rd rd'); [exact H|]. intros k Hk. apply HK. lia.
Qed.
Lemma pb3_MID2_same : forall v pos lyc Sc Wc memA rX memc mdc rX' memc' mdc',
  pb3_G v pos -> pb3_MID2 B v pos lyc Sc Wc memA rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (PB3_FI B v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000); (27, p_t v)]) ->
  pb3_MID2 B v pos lyc Sc Wc memA rX' memc' mdc'.
Proof.
intros v pos lyc Sc Wc memA rX memc mdc rX' memc' mdc' G (HJ & K & HRC & HSL & HFSH & HCN & HRG) HJ' KM HRG'.
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & _ & _).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in S1.
split; [exact HJ'|].
split.
{ apply (pb3_kept_trans v pos _ (rdW Wc memc)); [exact K|].
  split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
split; [apply (pb3_same_rconf _ _ _ _ KM); [lia | unfold seg_spec.SEG_C_SIZE in *; lia | exact HRC]|].
split.
{ apply (pb3_same_sl _ _ _ _ KM); [|exact HSL].
  intros o x Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; unfold PF_O_CN in *; lia|]). destruct Hin. }
split; [intros i Hi; rewrite KM; [exact (HFSH i Hi) | unfold kLowMemEnd, kHighShadowEnd in *; lia]|].
split; [intros i Hi; rewrite KM; [exact (HCN i Hi) | unfold PF_O_CN; lia]|].
exact HRG'.
Qed.

Ltac pb3_regk HS EE RG :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
  apply (pb3_rg _ _ _ _ RG); solve [unfold PB3_FI; pb3_in].

(* ---------- the piece: MID2 (0x88134) -> the check B#2 -> 0x88148 ---------- *)
Lemma pb3_s3a : forall v pos lyc Sc Wc memA rX memc mdc (Q : world SEGS -> config -> Prop),
  pb3_FA B v pos lyc Sc Wc memA -> pb3_MID2 B v pos lyc Sc Wc memA rX memc mdc ->
  (forall rX' memc' mdc', pb3_MID2 B v pos lyc Sc Wc memA rX' memc' mdc' ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x310)) rX' memc' mdc') Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x2fc)) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc memA rX memc mdc Q HFA HM Kc.
pose proof HFA as (HCX & G & Hin & EF & Hly & HSc & HPm & HOBJA & HSAV & HFL & HTF & Hfrs).
pose proof HM as (HJ & K2 & HRC & HSL & HFSH & HCN & HRG).
pose proof HJ as (HAR & _).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof HCX as (_ & _ & _ & Hc64 & _ & Ht64 & _ & _ & (fe & ((_ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & _ & HTD & _) & _)) & _).
assert (HOBJ : pf_obj B v lyc Sc (rdW Wc memc))
  by exact (pb3_keep_obj B v pos lyc Sc Wc memc mdc (rdW Wc memA) (rdW Wc memc) G HAR Hin EF HTD K2 HOBJA).
pose proof HOBJ as (O1 & O2 & O3 & _).
pose proof O2 as (_ & Ht63 & _ & HtRA & _).
destruct (pb3_heap_out B v pos lyc Sc Wc memc mdc (p_t v) (pf_len v) (p_t v) G HAR Hin EF O3
  ltac:(unfold pf_len; lia)) as (T1 & T2 & T3).
destruct (HtRA (p_t v) ltac:(unfold pf_len; lia)) as (s & Hs & Hok). unfold shadow_of_addr in Hs.
destruct (aview_byte SEGS (w_H Wc) memc _ _ Hs) as (_ & _ & _ & Hsr).
assert (Hs7 : 0 <= s <= 7) by (destruct Hok as [-> | [H1 H2]]; lia).
assert (R : forall r x, In (r, x) (PB3_FI B v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000);
    (27, p_t v)]) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hr; exact (pb3_rg rX _ r x HRG Hr)).
pose proof (pb3_seed3a Wc rX memc (p_t v) s (R 20 _ ltac:(unfold PB3_FI; pb3_in)) (R 27 _ ltac:(unfold PB3_FI; pb3_in))
  ltac:(lia) Hs Hs7) as HS.
set (E0 := Eimg (Ereg rX [w64 (SHADOW_OFF + p_t v / 8); w64 s])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
  by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E0 33 = w64 s) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
clearbody E0.
assert (E27 : ew E0 27 = w64 (p_t v)) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); apply R; unfold PB3_FI; pb3_in).
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x2fc)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x2fc))).
paj_run_sh RUNP HS HJ.
{ pb3_ro_awr. }
cbn [ms_mem mkst] in HFr, HG, HF.
pb3_clear_md.
assert (KMa : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
clear HFr HG HF.
psrr_branch_pi RUNP BR HS.
- (* s = 0: to 0x88148 *)
  clear Hc.
  paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x310).
  { pb3_ro_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb3_clear_md. rename ms into msP. rename ms0 into ms.
  assert (KMb : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KMa a Ha).
    apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem msP) (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  assert (QR : pf_rg (ms_regs ms) (PB3_FI B v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000); (27, p_t v)])).
  { unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regk HS EE HRG. }
  pmkst HS.
  apply Kc. exact (pb3_MID2_same v pos lyc Sc Wc memA rX memc mdc _ _ _ G HM HJ KMb QR).
- (* s <> 0: the slow path 0x891e4 *)
  assert (Hs0 : s <> 0).
  { intros ->. rewrite branch_eq_U, (U_atom E0 33 0 E33), U_lit in Hc by lia. discriminate Hc. }
  clear Hc.
  paj_run_sh RUNP HS HJ.
  { pb3_ro_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb3_clear_md. rename ms into msP. rename ms0 into ms.
  assert (KMb : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KMa a Ha).
    apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem msP) (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  clear HFr HG HF.
  psrr_branch_pi RUNP BR HS.
  + (* the error arm: t mod 8 >= s, against saddr_ok *)
    exfalso. exact (pb3_trap_b2 E0 (p_t v) s E27 ltac:(lia) E33 Hok Hs0 Hc).
  + clear Hc.
    paj_run_to_sh RUNTO HS HJ (AF_reac_segconf_parse_file + 0x310).
    { pb3_ro_awr. }
    cbn [ms_mem mkst] in HFr, HG, HF.
    pb3_clear_md. rename ms into msQ. rename ms0 into ms.
    assert (KMc : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha. rewrite <- (KMb a Ha).
      apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem msQ) (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
      intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
      destruct Hin'. }
    assert (QR : pf_rg (ms_regs ms) (PB3_FI B v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000); (27, p_t v)])).
    { unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd]; pb3_regk HS EE HRG. }
    pmkst HS.
    apply Kc. exact (pb3_MID2_same v pos lyc Sc Wc memA rX memc mdc _ _ _ G HM HJ KMc QR).
Qed.

End x.
End d.
