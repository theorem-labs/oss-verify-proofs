(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece
   B: the scan loop, cut L (B 0x86718) -> cut S (B 0x8676c), over the ONE image-B program listing
   (lib/B/Listing_prog.v) with the PA-listing engine YC80x / YC1fPx (paj_run_x, paj_run_to_x) over YCbqG's ajournal_x.
   Proves pnB_stmt (lib/B/Prog/PvB_NCut.v's
   statement).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search: `proof-index parse_value` (04:10Z, EXIT=0
   unpiped, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value; new proof
   justified. Template (read, not Required): image A's scan loop of ex_value,
   lib/A/Prog/S8aNumB.v.
   Code (neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s): 0x86718 .. 0x86724 the instrumented
   check of a1 (= s6), a load of the shadow byte and a compare, with its second compare at 0x86758 .. 0x8675c (the
   runner takes both; the error path errpath_load1 at 0x86764 is not reached: the byte lies in the text, whose range
   src_rd marks addressable); 0x86728 a6 := x[m]; 0x8672c .. 0x86730 the digit test `bltu (a6 - 48), a3 (10)`;
   0x86734 .. 0x86738 the range test `bltu a4 (58), (a6 - 43)` -> S; 0x8673c .. 0x86744 the mask bit
   `beqz ((a5 >> (a6 - 43)) & 1)` -> S; 0x86748 .. 0x86750 s6++, a1++, `bne s6, a2` -> L (the back edge);
   0x86754 `j 0x86768`; 0x86768 `mv s6, a2` -> S. One iteration is one runner pass from L to L or to S; the loop is nat
   induction on length x - m. The loop writes no memory (the one symbolic region has an empty write window), so
   pv_body, pv_reader0 and the Y + 24 spill carry over unchanged (same W, same mem) with the runner's journal, and so
   does L's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` (the memory normal form, a state fact of the cut): S states
   it at the same mem, so the plain runner serves and YSRrMemnorm.v's runner twin is not needed.
   Numerals: the cut pcs by PvB_NCut's names AF_pn_loop (20556) / AF_pn_scan (20640) (DERIVED: B pc - B_prog_base
   0x816cc); -48 -43 10 58 1 0 (WORD: the listing's immediates and the constants the arm loads at 0x866fc .. 0x86708);
   288230376218820621 (WORD: PvB_NCut's PN_MASK, the value the listing builds at 0x8670c); -1 (WORD: s5's result code
   at L); 8 24 32 (LENGTH: the &end spill Y + 24, its width, the end cell fa + 32, as pn_at_L states them); 4096, 255,
   256, 2 ^ 64 (LENGTH: address and byte ranges); 140737479966720 (LENGTH: YM05's CEIL_MAX, the bound of every run's
   alloc_ceiling); SHADOW_OFF + 2 ^ 44 - 1 (LENGTH: the shadow band); register numbers 2 .. 27 and atom numbers 22, 32
   (WORD / LENGTH: the env's register atoms and its first extra atom). Section hypotheses: LAWS only (at the head
   length hl, a Section Context, as YCbqG.v states AR_laws_x). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure: the loop's three byte tests as the runner leaves them, against PjGrammar.numch ---- *)
(* 0x86730 `bltu a7 (b - 48), a3 (10)`: taken on a digit *)
Definition nb_fd (b : Z) : bool :=
  branch_taken BC_LTU (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -48)) (Z_to_bv 64 10).
(* 0x86738 `bltu a4 (58), a6 (b - 43)`: taken (stop) when b - 43 is above 58 unsigned *)
Definition nb_fr (b : Z) : bool :=
  branch_taken BC_LTU (Z_to_bv 64 58) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -43)).
(* 0x86744 `beqz ((PN_MASK >> (b - 43)) & 1)`: taken (stop) when the mask bit is clear *)
Definition nb_ft (b : Z) : bool :=
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 288230376218820621)
    (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 b) + -43))) (Z_to_bv 64 1)) (Z_to_bv 64 0).

Definition nb_bytes256 : list Z := map Z.of_nat (seq 0 256).

Lemma nb_in_bytes256 : forall b, 0 <= b < 256 -> In b nb_bytes256.
Proof.
  intros b Hb. unfold nb_bytes256. apply in_map_iff. exists (Z.to_nat b). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma nb_forallb_bytes256 : forall (f : Z -> bool), forallb f nb_bytes256 = true -> forall b, 0 <= b < 256 -> f b = true.
Proof. intros f Hf b Hb. rewrite forallb_forall in Hf. exact (Hf b (nb_in_bytes256 b Hb)). Qed.

Lemma nb_bytes_all : forallb (fun b => Bool.eqb (PjGrammar.numch b) (nb_fd b || (negb (nb_fr b) && negb (nb_ft b))))
  nb_bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nb_numch : forall b, 0 <= b < 256 -> PjGrammar.numch b = nb_fd b || (negb (nb_fr b) && negb (nb_ft b)).
Proof.
  intros b Hb. pose proof (nb_forallb_bytes256 _ nb_bytes_all b Hb) as H. cbv beta in H.
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma nb_digit_numch : forall b, PjGrammar.digit b = true -> PjGrammar.numch b = true.
Proof. intros b H. unfold PjGrammar.numch. rewrite H. reflexivity. Qed.

Lemma nb_firstn_S : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [|h t IH]; intros n Hn; [cbn in Hn; lia|].
  destruct n as [|n]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. cbn in Hn. lia.
Qed.

Lemma nb_len_skipn : forall (l : list Z) n, length (skipn n l) = (length l - n)%nat.
Proof. induction l as [|h t IH]; intros n; destruct n; cbn; try reflexivity; apply IH. Qed.

Lemma nb_nth_skipn : forall (l : list Z) n m, nth m (skipn n l) 0 = nth (n + m) l 0.
Proof.
  induction l as [|h t IH]; intros n m.
  - rewrite skipn_nil. destruct m, n; reflexivity.
  - destruct n as [|n]; cbn [skipn]; [reflexivity | exact (IH n m)].
Qed.

Lemma nb_span_step : forall (x : list Z) j0 j, (j0 <= j < length x)%nat ->
  pn_span x j0 j -> PjGrammar.numch (nth j x 0) = true -> pn_span x j0 (S j).
Proof.
  intros x j0 j Hj HF Hn. unfold pn_span in *.
  replace (S j - j0)%nat with (S (j - j0)) by lia.
  rewrite nb_firstn_S by (rewrite nb_len_skipn; lia).
  apply Forall_app. split; [exact HF|]. constructor; [|constructor].
  rewrite nb_nth_skipn. replace (j0 + (j - j0))%nat with j by lia. exact Hn.
Qed.

(* the text from the first non-blank byte is a suffix of the whole text *)
Lemma nb_skip_suffix : forall l : list Z, exists n, PjGrammar.skip l = skipn n l.
Proof.
  induction l as [|h t IH]; [exists 0%nat; reflexivity|].
  cbn [PjGrammar.skip]. destruct (PjGrammar.ws h).
  - destruct IH as (n & Hn). exists (S n). rewrite Hn. reflexivity.
  - exists 0%nat. reflexivity.
Qed.

Lemma nb_text_byte : forall (tb : list Z) text p c y m,
  PjGrammar.skip (rest_atR tb text p) = c :: y -> (m < length (c :: y))%nat ->
  exists K, (K + length (c :: y) = length tb)%nat /\ nth m (c :: y) 0 = nth (K + m) tb 0.
Proof.
  intros tb text p c y m Hs Hm. unfold rest_atR in Hs.
  destruct (nb_skip_suffix (skipn (Z.to_nat (p - text)) tb)) as (n & Hn).
  rewrite Hn, skipn_skipn in Hs.
  exists (n + Z.to_nat (p - text))%nat. split.
  - pose proof (nb_len_skipn tb (n + Z.to_nat (p - text))) as HL. rewrite Hs in HL.
    cbn [length] in HL |- *. lia.
  - rewrite <- Hs. apply nb_nth_skipn.
Qed.

Lemma nb_ne_lit : forall u v, 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 u) (Z_to_bv 64 v) = negb (u =? v).
Proof. intros u v Hu Hv. cbn [branch_taken]. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma nb_w64 : forall u v, u = v -> Z_to_bv 64 u = w64 v.
Proof. intros u v ->. reflexivity. Qed.

(* ---- the symbolic state at L (pc 20556): a1 the atom of s6 (p1 + m), the loop constants a3 a4 a5 and s7
   (SHADOW_OFF) literal, the byte x[m] the one-byte read-only region at s6 holding atom 32 (the env's extra word); the
   shadow byte of a1 is the runner's token, its obligation src_rd's ---- *)
Definition NB_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 13%bv (SLit 10)) 14%bv (SLit 58))
    15%bv (SLit PN_MASK)) 23%bv (SLit SHADOW_OFF)) 11%bv (SOff 22 0).
Definition NB_mem : smem := [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]].
(* atom 22's range: [4096, CEIL_MAX] (LENGTH: YM05's bound on every run's alloc_ceiling) *)
Definition NB_facts : facts := mkFacts [(22%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF 0 255 0)] [] [].
Definition NB_ss : sstate := mkSS AF_pn_loop NB_regs NB_mem None NB_facts.
Definition NB_Bx : sv := SLit SHADOW_OFF.
Definition NB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the registers the loop never writes, among those L / S name (13, 14, 15, 23 are literals of NB_regs) *)
Definition NB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 10; 12; 18; 19; 20; 21; 24; 26; 27]%bv.

Definition nb_kept_ok (ss : sstate) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NB_KEPT.
Definition nb_resv_none (ss : sstate) : bool := match ss_resv ss with None => true | Some _ => false end.
(* the three cut shapes the runner stops in: back at L with s6 = a1 = p1 + m + 1; at S with s6 = p1 + m (a stop
   byte); at S through 0x86768 with s6 = a2 = tend *)
Definition nb_shape_loop (ss : sstate) : bool :=
  (ss_pc ss =? AF_pn_loop) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 1) && sv_eqb (sr_get (ss_regs ss) 11%bv) (SOff 22 1) &&
  sv_eqb (sr_get (ss_regs ss) 13%bv) (SLit 10) && sv_eqb (sr_get (ss_regs ss) 14%bv) (SLit 58) &&
  sv_eqb (sr_get (ss_regs ss) 15%bv) (SLit PN_MASK) &&
  sv_eqb (sr_get (ss_regs ss) 23%bv) (SLit SHADOW_OFF).
Definition nb_shape_stop (ss : sstate) : bool :=
  (ss_pc ss =? AF_pn_scan) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 22 0) && sv_eqb (sr_get (ss_regs ss) 23%bv) (SLit SHADOW_OFF).
Definition nb_shape_end (ss : sstate) : bool :=
  (ss_pc ss =? AF_pn_scan) && nb_resv_none ss && nb_kept_ok ss &&
  sv_eqb (sr_get (ss_regs ss) 22%bv) (SOff 12 0) && sv_eqb (sr_get (ss_regs ss) 23%bv) (SLit SHADOW_OFF).

(* the loop writes nothing: every runner pass keeps the whole memory *)
Lemma nb_frame : forall E ss (m m' : word -> option byte), frame_of E (ss_mem ss) m m' -> ss_mem ss = NB_mem -> m' = m.
Proof.
  intros E ss m m' HF Hs. apply functional_extensionality. intros x. apply HF. rewrite Hs.
  intros (r & Hin & Hr). unfold NB_mem in Hin. destruct Hin as [<-|[]]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Ltac nb_agree HAE :=
  lazymatch goal with
  | |- env_agree ?kk _ (ewset ?X ?n ?v) =>
      apply (YP03.env_agree_trans kk _ X); [nb_agree HAE | apply (YP03.env_agree_le kk n); [lia | apply env_agree_ewset]]
  | |- _ => exact HAE
  end.

Ltac nb_mem mem0 :=
  lazymatch goal with HF : frame_of _ _ _ (ms_mem _) |- _ =>
    let Hm := fresh "Hm" in
    pose proof (nb_frame _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm; clear HF
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  try match goal with
  | Hold : ms_mem ?m0 = mem0, Hnew : ms_mem _ = ms_mem ?m0 |- _ => rewrite Hold in Hnew; clear Hold
  end;
  repeat match goal with HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress (rewrite ?wvb_collapse in HJ) end.

Section d.
Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the kit's allocator laws (Section hypothesis of every walk over ajournal_x), at the harness block's head length hl *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation FIN en := (pv_FINK (SK := SK) B ARx en).
#[local] Abbreviation AJ en pos lyc Sc W mem md k := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx
  (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en)
  (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W mem md k).

(* L's facts with the machine state's parts named (pn_at_L's body after `ms = pn_ms ...`) *)
Definition nb_L (en : PvEnt) (W' : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (mdc : Model)
    (Y fa fl pos : Z) (lyc : alayout) (Sc : astate) (k c : Z) (y : list Z) (m : nat) : Prop :=
  let x := c :: y in let p1 := pn_p1 en x in
  pn_base en regs Y fa c y /\
  pv_body (SK := SK) B ARx en Y fa fl pos pv_shadow_open lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_reader0 B en pos p1 lyc Sc W' mem /\ val_mem SEGS (rdW W' mem) (Y + 24) 8 (fa + 32) /\
  getr regs 21 = w64 (-1) /\ getr regs 10 = w64 p1 /\ getr regs 12 = w64 (pe_text en + pe_len en) /\
  getr regs 13 = w64 10 /\ getr regs 14 = w64 58 /\ getr regs 15 = w64 PN_MASK /\
  pn_lead x (pn_sg c) /\ (pn_sg c <= m < length x)%nat /\ pn_span x (pn_sg c) m /\
  getr regs 22 = w64 (p1 + Z.of_nat m) /\ getr regs 11 = w64 (p1 + Z.of_nat m) /\
  YStrtodRowX.aj_memnorm SEGS mem.

Lemma nb_L_of : forall en W ms md, pn_at_L (SK := SK) B ARx en W ms md ->
  exists regs mem Y fa fl pos lyc Sc k c y m,
  ms = pn_ms fx0 regs AF_pn_loop mem /\ nb_L en W regs mem md Y fa fl pos lyc Sc k c y m.
Proof.
  intros en W ms md (regs & mem & Y & fa & fl & pos & lyc & Sc & k & c & y & m & Hms & H).
  exists regs, mem, Y, fa, fl, pos, lyc, Sc, k, c, y, m. split; [exact Hms | exact H].
Qed.

Lemma nb_reg_of : forall (H : word -> bool) E ss ms (r : bv 5) e,
  @st_ok_pi SEGS VAL fx0 E ss (restrict H ms) -> sv_eqb (sr_get (ss_regs ss) r) e = true ->
  getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS Hq. apply sv_eqb_eq in Hq. rewrite <- Hq. exact (st_ok_pi_restrict_reg H E ss ms r HS). Qed.

(* ---- the cut facts at the next cut, from L's and the runner's (no machine state here) ---- *)
Lemma nb_base_keep : forall en regs regs' Y fa c y,
  pn_base en regs Y fa c y -> (forall r, In r NB_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 23 = Z_to_bv 64 SHADOW_OFF -> pn_base en regs' Y fa c y.
Proof.
  intros en regs regs' Y fa c y (HKR & R9 & R19 & R20 & R24 & Hsk) HK Q23.
  destruct HKR as (R2 & R8 & R18 & R26 & R27 & _ & R3 & R4).
  refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj Q23 (conj _ _)))))))
    (conj _ (conj _ (conj _ (conj _ Hsk))))).
  all: lazymatch goal with |- getr _ ?r = _ => rewrite (HK r ltac:(cbv; tauto)); assumption end.
Qed.

Lemma nb_mk_L : forall en W regs regs' mem md md' Y fa fl pos lyc Sc k c y m,
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  AJ en pos lyc Sc W mem md' k ->
  (forall r, In r NB_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 22 = Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m + 1) ->
  getr regs' 11 = Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m + 1) ->
  getr regs' 13 = Z_to_bv 64 10 -> getr regs' 14 = Z_to_bv 64 58 ->
  getr regs' 15 = Z_to_bv 64 PN_MASK -> getr regs' 23 = Z_to_bv 64 SHADOW_OFF ->
  PjGrammar.numch (nth m (c :: y) 0) = true -> (S m < length (c :: y))%nat ->
  nb_L en W regs' mem md' Y fa fl pos lyc Sc k c y (S m).
Proof.
  intros en W regs regs' mem md md' Y fa fl pos lyc Sc k c y m HL HJ' HK Q22 Q11 Q13 Q14 Q15 Q23 Hn Hlt.
  unfold nb_L in HL |- *. cbv zeta in HL |- *.
  destruct HL as (HB & HBODY & HR0 & HY24 & R21 & R10 & R12 & R13 & R14 & R15 & HLD & Hm & HSP & R22 & R11 & HMN).
  destruct HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  refine (conj (nb_base_keep _ _ _ _ _ _ _ HB HK Q23)
    (conj (conj HFRM (conj HinF (conj Efa (conj Efl (conj HJ' HWIN)))))
    (conj HR0 (conj HY24 (conj _ (conj _ (conj _ (conj Q13 (conj Q14 (conj Q15
    (conj HLD (conj _ (conj _ (conj _ (conj _ HMN))))))))))))))).
  - rewrite (HK 21%bv ltac:(cbv; tauto)). exact R21.
  - rewrite (HK 10%bv ltac:(cbv; tauto)). exact R10.
  - rewrite (HK 12%bv ltac:(cbv; tauto)). exact R12.
  - lia.
  - apply nb_span_step; [lia | exact HSP | exact Hn].
  - rewrite Q22. apply nb_w64. lia.
  - rewrite Q11. apply nb_w64. lia.
Qed.

Lemma nb_mk_S : forall en W regs regs' mem md md' Y fa fl pos lyc Sc k c y m m',
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  AJ en pos lyc Sc W mem md' k ->
  (forall r, In r NB_KEPT -> getr regs' r = getr regs r) -> getr regs' 23 = Z_to_bv 64 SHADOW_OFF ->
  pn_span (c :: y) (pn_sg c) m' -> (pn_sg c < m' <= length (c :: y))%nat -> pn_stop (c :: y) m' ->
  getr regs' 22 = Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m') ->
  pn_at_S (SK := SK) B ARx en W (pn_ms fx0 regs' AF_pn_scan mem) md'.
Proof.
  intros en W regs regs' mem md md' Y fa fl pos lyc Sc k c y m m' HL HJ' HK Q23 HSP' Hb' Hst Q22.
  unfold nb_L in HL. cbv zeta in HL.
  destruct HL as (HB & HBODY & HR0 & HY24 & R21 & R10 & R12 & _ & _ & _ & HLD & _ & _ & _ & _ & HMN).
  destruct HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  exists regs', mem, Y, fa, fl, pos, lyc, Sc, k, c, y, m'. cbv zeta.
  refine (conj eq_refl (conj (nb_base_keep _ _ _ _ _ _ _ HB HK Q23)
    (conj (conj HFRM (conj HinF (conj Efa (conj Efl (conj HJ' HWIN)))))
    (conj HR0 (conj HY24 (conj _ (conj _ (conj _ (conj HLD (conj Hb' (conj HSP' (conj Hst (conj Q22 HMN))))))))))))).
  - rewrite (HK 21%bv ltac:(cbv; tauto)). exact R21.
  - rewrite (HK 10%bv ltac:(cbv; tauto)). exact R10.
  - rewrite (HK 12%bv ltac:(cbv; tauto)). exact R12.
Qed.

(* ---- the loop statement at a bounded remaining length ---- *)
Definition nb_KLm (en : PvEnt) (n : nat) : Prop :=
  forall W regs mem md Y fa fl pos lyc Sc k c y m,
  (length (c :: y) - m)%nat = n -> nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  SRr SEGS W (mkCfg (pn_ms fx0 regs AF_pn_loop mem) md) (FIN en).

(* the text bounds L carries (pv_reader0's pj_in_okR) *)
Lemma nb_p1_range : forall en W regs mem md Y fa fl pos lyc Sc k c y m,
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  0 < pn_p1 en (c :: y) /\ pn_p1 en (c :: y) + Z.of_nat (length (c :: y)) = pe_text en + pe_len en /\
  pe_text en + pe_len en < 2 ^ 62.
Proof.
  intros en W regs mem md Y fa fl pos lyc Sc k c y m HL.
  unfold nb_L in HL. cbv zeta in HL.
  destruct HL as (_ & _ & HR0 & _).
  destruct HR0 as (_ & _ & _ & _ & HIN & _).
  destruct HIN as (_ & _ & _ & _ & _ & Htx0 & Htx62 & Hp1r & _).
  unfold pn_p1 in *. lia.
Qed.

(* ---- closing a runner pass at a cut: the machine state from the symbolic one by its shape ---- *)
Lemma nb_close_loop : forall en n W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md',
  nb_KLm en n -> (length (c :: y) - m)%nat = S n ->
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  @st_ok_pi SEGS VAL fx0 E ss (restrict (w_H W) ms) -> nb_shape_loop ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ en pos lyc Sc W (ms_mem ms) md' k ->
  PjGrammar.numch (nth m (c :: y) 0) = true -> (S m < length (c :: y))%nat ->
  SRr SEGS W (mkCfg ms md') (FIN en).
Proof.
  intros en n W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md' IH Hmn HL HS Hsh HA Hm HJ Hn Hlt.
  unfold nb_shape_loop in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[[[[[Hpc Hrv] Hkp] S22] S11] S13] S14] S15] S23].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (nb_p1_range en W regs mem md Y fa fl pos lyc Sc k c y m HL) as (Hp0 & Hp1e & Hp62).
  pose proof HL as HL'. unfold nb_L in HL'. cbv zeta in HL'.
  destruct HL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmr & _ & R22 & _).
  destruct HA as [HA0 _].
  assert (E22 : ew E 22 = Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m)).
  { rewrite HA0 by lia. rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl). exact R22. }
  pose proof (nb_reg_of _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of _ E ss ms 11%bv _ HS S11) as Q11.
  pose proof (nb_reg_of _ E ss ms 13%bv _ HS S13) as Q13.
  pose proof (nb_reg_of _ E ss ms 14%bv _ HS S14) as Q14.
  pose proof (nb_reg_of _ E ss ms 15%bv _ HS S15) as Q15.
  pose proof (nb_reg_of _ E ss ms 23%bv _ HS S23) as Q23.
  cbn [sv_denot] in Q22, Q11, Q13, Q14, Q15, Q23.
  rewrite E22, unsigned_lit_small in Q22, Q11 by lia.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  exact (IH W (ms_regs ms) mem md' Y fa fl pos lyc Sc k c y (S m) ltac:(lia)
    (nb_mk_L en W regs (ms_regs ms) mem md md' Y fa fl pos lyc Sc k c y m HL HJ HK Q22 Q11 Q13 Q14 Q15 Q23 Hn Hlt)).
Qed.

Lemma nb_close_stop : forall en W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md',
  pnK (SK := SK) B ARx en (pn_at_S (SK := SK) B ARx en) ->
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  @st_ok_pi SEGS VAL fx0 E ss (restrict (w_H W) ms) -> nb_shape_stop ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ en pos lyc Sc W (ms_mem ms) md' k ->
  PjGrammar.numch (nth m (c :: y) 0) = false ->
  SRr SEGS W (mkCfg ms md') (FIN en).
Proof.
  intros en W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md' HKS HL HS Hsh HA Hm HJ Hn.
  unfold nb_shape_stop in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[Hpc Hrv] Hkp] S22] S23].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof HL as HL'. unfold nb_L in HL'. cbv zeta in HL'.
  destruct HL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLD & Hmr & HSP & R22 & _).
  destruct HA as [HA0 _].
  pose proof (nb_reg_of _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of _ E ss ms 23%bv _ HS S23) as Q23.
  cbn [sv_denot] in Q22, Q23.
  rewrite HA0 in Q22 by lia.
  rewrite (ew_Ereg_nat regs extra 22 22%bv eq_refl), R22, Z.add_0_r, Z_to_bv_bv_unsigned in Q22.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  apply HKS.
  apply (nb_mk_S en W regs (ms_regs ms) mem md md' Y fa fl pos lyc Sc k c y m m HL HJ HK Q23 HSP);
    [| right; exact Hn | exact Q22].
  destruct (Nat.eq_dec m (pn_sg c)) as [Ej | Nj]; [|lia].
  exfalso. destruct HLD as (_ & Hd & _). rewrite <- Ej in Hd. rewrite (nb_digit_numch _ Hd) in Hn. discriminate.
Qed.

Lemma nb_close_end : forall en W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md',
  pnK (SK := SK) B ARx en (pn_at_S (SK := SK) B ARx en) ->
  nb_L en W regs mem md Y fa fl pos lyc Sc k c y m ->
  @st_ok_pi SEGS VAL fx0 E ss (restrict (w_H W) ms) -> nb_shape_end ss = true ->
  env_agree 32 (Ereg regs extra) E -> ms_mem ms = mem -> AJ en pos lyc Sc W (ms_mem ms) md' k ->
  PjGrammar.numch (nth m (c :: y) 0) = true -> S m = length (c :: y) ->
  SRr SEGS W (mkCfg ms md') (FIN en).
Proof.
  intros en W regs mem md Y fa fl pos lyc Sc k c y m extra E ss ms md' HKS HL HS Hsh HA Hm HJ Hn Hend.
  unfold nb_shape_end in Hsh. repeat rewrite andb_true_iff in Hsh.
  destruct Hsh as [[[[Hpc Hrv] Hkp] S22] S23].
  apply Z.eqb_eq in Hpc.
  assert (Hrv' : ss_resv ss = None) by (unfold nb_resv_none in Hrv; destruct (ss_resv ss); [discriminate | reflexivity]).
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv') as Hms.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs extra NB_KEPT HS HA Hkp) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (nb_p1_range en W regs mem md Y fa fl pos lyc Sc k c y m HL) as (Hp0 & Hp1e & Hp62).
  pose proof HL as HL'. unfold nb_L in HL'. cbv zeta in HL'.
  destruct HL' as (_ & _ & _ & _ & _ & _ & R12 & _ & _ & _ & HLD & Hmr & HSP & _ & _).
  destruct HA as [HA0 _].
  pose proof (nb_reg_of _ E ss ms 22%bv _ HS S22) as Q22.
  pose proof (nb_reg_of _ E ss ms 23%bv _ HS S23) as Q23.
  cbn [sv_denot] in Q22, Q23.
  rewrite HA0 in Q22 by lia.
  rewrite (ew_Ereg_nat regs extra 12 12%bv eq_refl), R12, Z.add_0_r, Z_to_bv_bv_unsigned in Q22.
  rewrite Hms, Hpc, Hm. rewrite Hm in HJ.
  apply HKS.
  apply (nb_mk_S en W regs (ms_regs ms) mem md md' Y fa fl pos lyc Sc k c y m (S m) HL HJ HK Q23);
    [| lia | left; exact Hend |].
  - apply nb_span_step; [lia | exact HSP | exact Hn].
  - assert (Etend : pe_text en + pe_len en = pn_p1 en (c :: y) + Z.of_nat (S m)) by lia.
    rewrite Q22, Etend. reflexivity.
Qed.

(* ---- one iteration: L at m -> L at m + 1 (the induction hypothesis) or S ---- *)
Lemma nb_step : forall en, pnK (SK := SK) B ARx en (pn_at_S (SK := SK) B ARx en) ->
  forall n, nb_KLm en n -> nb_KLm en (S n).
Proof.
  intros en HKS n IH W regs mem md Y fa fl pos lyc Sc k c y m Hmn HL.
  pose proof (nb_p1_range en W regs mem md Y fa fl pos lyc Sc k c y m HL) as (Hp0 & Hp1e & Hp62).
  pose proof HL as HL'. unfold nb_L in HL'. cbv zeta in HL'.
  destruct HL' as (HB & HBODY & HR0 & _ & R21 & R10 & R12 & R13 & R14 & R15 & HLD & Hm & HSP & R22 & R11 & _).
  pose proof HB as (HKR & _ & _ & _ & _ & Hskip & _).
  pose proof HKR as (_ & _ & _ & _ & _ & R23 & _).
  pose proof HBODY as (_ & _ & _ & _ & HJ & _).
  pose proof HR0 as (_ & _ & _ & _ & HIN & HSRC & _).
  pose proof HIN as (_ & _ & _ & _ & _ & Htx0 & Htx62 & Hp1r & Hlen & HG8 & _).
  pose proof HSRC as (_ & Htx4096 & Htxceil & _ & HRA & _).
  pose proof (@alloc_ceiling_value rc) as Hceil.
  (* the byte x[m], in the text *)
  unfold pe_rest in Hskip.
  destruct (nb_text_byte (pe_tb en) (pe_text en) (pe_p en) c y m Hskip ltac:(lia)) as (K & HKl & Hnth).
  assert (Hp1 : pn_p1 en (c :: y) = pe_text en + Z.of_nat K) by (unfold pn_p1 in *; lia).
  destruct (HG8 (K + m)%nat ltac:(lia)) as [Vb Hb].
  rewrite <- Hnth in Vb, Hb.
  replace (pe_text en + Z.of_nat (K + m)) with (pn_p1 en (c :: y) + Z.of_nat m) in Vb by lia.
  set (b := nth m (c :: y) 0) in *.
  set (p1 := pn_p1 en (c :: y)) in *.
  remember (Eimg (PI := PA) (Ereg regs [Z_to_bv 64 b])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 b]) E)
    by (subst E; split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r).
  { intros i r Hi. subst E. pose proof (u5_range r) as Hr. rewrite Eimg_low by (unfold A_TEXT; lia).
    apply ew_Ereg_nat. exact Hi. }
  assert (E22 : ew E 22 = Z_to_bv 64 (p1 + Z.of_nat m)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
  assert (E12 : ew E 12 = Z_to_bv 64 (pe_text en + pe_len en)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
  assert (E32 : ew E 32 = Z_to_bv 64 b).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  unfold pn_ms.
  assert (HS : @st_ok_pi SEGS VAL fx0 E NB_ss
     (restrict (w_H W) (@YK11.mkst fx0 regs (Z_to_bv 64 (BASE + AF_pn_loop)) mem (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold NB_ss. apply pa_entry_st_ok_full.
    - unfold NB_regs.
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; exact R11].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R23].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R15].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R14].
      apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; exact R13].
      subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold NB_mem. constructor; [|constructor]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (p1 + Z.of_nat m) 0 1%N (SOff 32 0) b).
      + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + cbn. lia.
      + rewrite Z.add_0_r. exact Vb.
    - cbn. tauto.
    - split; [|split; exact I]. cbn [NB_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E32, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  clear HE EE.
  assert (SHOK : sh_ok SEGS NB_Bx [] E (mrestrict (w_H W) mem)) by constructor.
  pose proof (@paj_run_x fx0 rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS) as RUN.
  pose proof (@paj_run_to_x fx0 rc SK B_prog_listing PL_prog_B PA B (@prh_pst prh_img_B) ARx _ LAWS) as RUNTO.
  pose proof (@paj_branch fx0 rc B_prog_listing PA) as BR.
  (* 0x86718 .. 0x86730: the shadow check of a1 (token, obligation: x[m] addressable), x[m], the digit test *)
  paj_run_tok_x RUN HS HJ SHOK NB_Bspan.
  1: { cbn [ms_mem YK11.mkst]. rewrite (U_atom E 22 (p1 + Z.of_nat m) E22) by lia.
       eapply obl_of_range; [exact HRA | | lia | lia].
       unfold NB_Bx. rewrite U_SLit. apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
  1: { awr_ok_tac. }
  nb_mem mem.
  psrr_branch_tok RUN BR HS SHOK NB_Bspan.
  - (* a digit: 0x86748, s6++, a1++, the back edge *)
    cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite E32 in Hc. change (nb_fd b = true) in Hc.
    assert (Hn : PjGrammar.numch b = true) by (rewrite (nb_numch _ Hb), Hc; reflexivity).
    clear Hc.
    paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
    psrr_branch_tok RUN BR HS SHOK NB_Bspan;
      cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc; rewrite !unsigned_lit_small in Hc by lia;
      rewrite Z.add_0_r, nb_ne_lit in Hc by lia.
    + apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_loop; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_loop en n W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
          IH Hmn HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
      end.
    + apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_scan; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_end en W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
          HKS HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
      end.
  - (* not a digit: the range test b - 43 <= 58 *)
    cbn [sv_denot ew ewset Nat.eqb] in Hc. rewrite E32 in Hc. change (nb_fd b = false) in Hc.
    rename Hc into Hd.
    paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
    psrr_branch_tok RUN BR HS SHOK NB_Bspan;
      cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E32 in Hc.
    + (* out of range: stop at m *)
      change (nb_fr b = true) in Hc.
      assert (Hn : PjGrammar.numch b = false) by (rewrite (nb_numch _ Hb), Hd, Hc; reflexivity).
      paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_scan; [awr_ok_tac|]. nb_mem mem.
      lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
        eapply (nb_close_stop en W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
          HKS HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn]
      end.
    + (* in range: the mask bit *)
      change (nb_fr b = false) in Hc. rename Hc into Hr.
      paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
      psrr_branch_tok RUN BR HS SHOK NB_Bspan;
        cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E32 in Hc.
      * (* the bit is clear: stop at m *)
        change (nb_ft b = true) in Hc.
        assert (Hn : PjGrammar.numch b = false) by (rewrite (nb_numch _ Hb), Hd, Hr, Hc; reflexivity).
        paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_scan; [awr_ok_tac|]. nb_mem mem.
        lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
          eapply (nb_close_stop en W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
            HKS HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn]
        end.
      * (* the bit is set ('+' '-' '.' 'E' 'e'): 0x86748 and the back edge *)
        change (nb_ft b = false) in Hc.
        assert (Hn : PjGrammar.numch b = true) by (rewrite (nb_numch _ Hb), Hd, Hr, Hc; reflexivity).
        clear Hc.
        paj_run_tok_x RUN HS HJ SHOK NB_Bspan; [awr_ok_tac|]. nb_mem mem.
        psrr_branch_tok RUN BR HS SHOK NB_Bspan;
          cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite E22, E12 in Hc; rewrite !unsigned_lit_small in Hc by lia;
          rewrite Z.add_0_r, nb_ne_lit in Hc by lia.
        -- apply negb_true_iff, Z.eqb_neq in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_loop; [awr_ok_tac|]. nb_mem mem.
           lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
             eapply (nb_close_loop en n W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
               IH Hmn HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
           end.
        -- apply negb_false_iff, Z.eqb_eq in Hc.
           paj_run_to_tok_x RUNTO HS HJ SHOK NB_Bspan AF_pn_scan; [awr_ok_tac|]. nb_mem mem.
           lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss (restrict _ ?ms) |- _ =>
             eapply (nb_close_end en W regs mem md Y fa fl pos lyc Sc k c y m [Z_to_bv 64 b] E' ss ms _
               HKS HL HS ltac:(vm_compute; reflexivity) ltac:(nb_agree HAE)); [assumption | exact HJ | exact Hn | lia]
           end.
Qed.

Lemma nb_base : forall en, nb_KLm en 0.
Proof.
  intros en W regs mem md Y fa fl pos lyc Sc k c y m Hmn HL. exfalso.
  unfold nb_L in HL. cbv zeta in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _). lia.
Qed.

Lemma nb_all : forall en, pnK (SK := SK) B ARx en (pn_at_S (SK := SK) B ARx en) -> forall n, nb_KLm en n.
Proof. intros en HKS n. induction n as [|n IHn]; [apply nb_base | exact (nb_step en HKS n IHn)]. Qed.

(* sub-piece B: L -> S (PvB_NCut.v pnB_stmt) *)
Theorem pnB : pnB_stmt (SK := SK) B ARx.
Proof.
  intros en _ HKS W ms md HL.
  destruct (nb_L_of en W ms md HL) as (regs & mem & Y & fa & fl & pos & lyc & Sc & k & c & y & m & -> & HL').
  exact (nb_all en HKS _ W regs mem md Y fa fl pos lyc Sc k c y m eq_refl HL').
Qed.
End d.
