(* preset_base64_decode (fs.asan 0x8481c), part L of the Theorem Labs lane walk (a Theorem Labs lane): the canonical symbolic states of the
   loop (the head 0x848bc, the return of memchr 0x848fc, the success tail 0x849d8) and the generic builder of their st_ok
   from the loop-head facts of FSW_dec_defs.v. SCRATCH during the walk (owner a Theorem Labs lane); a Theorem Labs lane integrates it.
   MEASURED with the token engine over FSW_writer_tbl.fsw_wr_tbl (scratch FSW_dec_Lm.v, removed):
   - the inline check of the text byte reads the shadow of s4 (atom 20) with base s5 (atom 21, = SHADOW_OFF), so the
     token engine's Bx is SOff 21 0; the byte itself is loaded through s2 (atom 18);
   - from the head with c in [0, 255]: `bltu s9, c` (0x848d0), `(mask >> c) & 1` (0x848dc), `c == 61` (0x848e0),
     `c == 0` (0x848ec) are symbolic branches; whitespace and '=' return to 0x848bc (s2, s4 + 1; '=': s10 + 1); the other
     bytes call memchr at PC_memchr with a0 = s3 (G_B64), a1 = c, a2 = 65, ra = 0x848fc;
   - the NUL: `bge 5, s8` (0x84970; taken -> fuzz_free), `s7 & ~(-1 << s8) != 0` (0x849d0; -> fuzz_free), `blt 2, s10`
     (0x849d8; -> fuzz_free), then lenp is reloaded from the frame slot (chunk 0 = atom 33), its shadow is checked
     (base s5) and n is stored to it; fuzz_free is reached at A_fuzz_free with a0 = q, ra = 0x8497c;
   - after memchr (a0 = r): `beqz r` -> fuzz_free; `bnez s10` -> fuzz_free; s7 := (r - G_B64) | (s7 <<w 6), s8 + 6 or,
     when s8 >= 2, the byte srlw(s7, s8 - 2) stored at s1 + s6 (an alias of atom 47), s6 + 1, s8 - 2; back to 0x848bc.
   Atoms of the canonical states: 0..31 the registers at the cut (Ereg), 32 the shadow base, 33 lenp (frame word 0),
   34 + j the entry value of the j-th register of dec_saved (frame word 1 + j), 47 the cut's own atom (the text byte at
   the head, q + n after memchr). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pcs and bounds ---- *)
Definition DEC_EXIT_PAD : Z := 0x849d8.          (* `blt 2, s10` of the NUL exit (MEASURED 543192) *)
Definition DEC_CEIL : Z := 0x7fffff800000.       (* the upper bound of alloc_ceiling (YCbq.v asan_consts) *)

(* ---- the frame chunks: word 0 holds lenp (atom 33), word 1 + j the entry value of nth j dec_saved (atom 34 + j) ---- *)
Definition decL_cs : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 38 0));
   YP09.mkChunk 48 (CVal 8 (SOff 39 0)); YP09.mkChunk 56 (CVal 8 (SOff 40 0)); YP09.mkChunk 64 (CVal 8 (SOff 41 0));
   YP09.mkChunk 72 (CVal 8 (SOff 42 0)); YP09.mkChunk 80 (CVal 8 (SOff 43 0)); YP09.mkChunk 88 (CVal 8 (SOff 44 0));
   YP09.mkChunk 96 (CVal 8 (SOff 45 0)); YP09.mkChunk 104 (CVal 8 (SOff 46 0))].
(* the extra atoms 33 .. 46 of every cut's env (after fs_extraT's atom 32) *)
Definition decL_xs (d : DE) : list word := Z_to_bv 64 (d_lenp d) :: map (fun r => getr (d_regs d) r) dec_saved.

(* ---- the extra regions ---- *)
(* the text byte at the head: one read-only byte at s2 (atom 18), its value atom 47 *)
Definition decL_txr : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 47 0))].
(* the byte q + n the iteration after memchr may store (atom 47, an alias of s1 + s6) *)
Definition decL_str : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [].
(* *lenp, the 8 bytes the success tail stores (real-stack placement only), at atom 33 *)
Definition decL_lpr : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].

(* ---- the token engine's shadow base and shadow entries ---- *)
Definition decL_Bx : sv := SOff 21 0.
Definition decL_hSH : list shent := [mkSHE 20 0 1].
Definition decL_mSH : list shent := [mkSHE 47 0 1].
Definition decL_lSH : list shent := [mkSHE 33 0 8].

(* ---- the atom facts of the s-registers at every cut (pad in [plo, phi], bits in [blo, bhi]) ---- *)
Definition decL_sgf (plo phi blo bhi : Z) : list (nat * afact) :=
  [(8%nat, mkAF DEC_WSMASK DEC_WSMASK 0); (9%nat, mkAF (4096 + HEAD) DEC_CEIL 4);
   (18%nat, mkAF 4096 DEC_CEIL 0); (19%nat, mkAF G_B64 G_B64 0); (20%nat, mkAF 4096 DEC_CEIL 0);
   (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (22%nat, mkAF 0 (2 ^ 30) 0); (23%nat, mkAF 0 (2 ^ 64 - 1) 0);
   (24%nat, mkAF blo bhi 1); (25%nat, mkAF 61 61 0); (26%nat, mkAF plo phi 0); (27%nat, mkAF 2 2 0)].

(* ---- the canonical states ---- *)
Definition decL_hgf : list (nat * afact) := (47%nat, mkAF 0 255 0) :: decL_sgf 0 (2 ^ 28) 0 6.
Definition decL_hss : sstate := fss_retT DEC_HEAD DEC_F decL_cs [decL_txr] decL_hgf.
Definition decL_mgf : list (nat * afact) := (47%nat, mkAF 4096 (DEC_CEIL - 1) 0) :: decL_sgf 0 (2 ^ 28) 0 6.
Definition decL_mss0 : sstate := fss_retT DEC_RA_MEMCHR DEC_F decL_cs [decL_str] decL_mgf.
Definition decL_mss : sstate :=
  mkSS DEC_RA_MEMCHR sr_atoms (ss_mem decL_mss0) None
    (mkFacts (f_atoms (ss_facts decL_mss0)) [] [(SAlu ALU_ADD (SOff 9 0) (SOff 22 0), SOff 47 0)]).
Definition decL_lgf : list (nat * afact) := (33%nat, mkAF (2 ^ 46) (2 ^ 47 - 8) 3) :: decL_sgf 0 2 0 6.
Definition decL_lss : sstate := fss_retT DEC_EXIT_PAD DEC_F decL_cs [decL_lpr] decL_lgf.

Section L0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

(* the memory facts of a cut (dec_head's, but the frame words): the decode block, its shadow, the allocator statics, the
   caller's objects (dec_kept) and the bytes decoded so far *)
Definition decL_memf (d : DE) (q : Z) (six : list Z) (Wc : world tfibsegs) (lyc : alayout) (Sc : astate)
    (memc : word -> option byte) : Prop :=
  fs_rblock tfibsegs B lyc Sc Wc memc q (d_n d) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF q (d_n d) /\
  fs_glob tfibsegs Wc memc (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) /\
  dec_kept B d Wc memc /\ zbytes_at tfibsegs Wc memc q (WriterSpec.six_bytes six).

(* the env of a cut: the registers, the shadow base, lenp and the 13 saved entry values, then the cut's own atoms *)
Definition decL_E (d : DE) (regs : bvmap 5 word) (ex : list word) : env := Ereg regs (fs_extraT ++ decL_xs d ++ ex).

Lemma decL_E_lenp : forall d regs ex, ew (decL_E d regs ex) 33 = Z_to_bv 64 (d_lenp d).
Proof. intros d regs ex. unfold decL_E. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma decL_E_ex : forall d regs ex j, ew (decL_E d regs ex) (47 + j) = nth j ex (Z_to_bv 64 0).
Proof.
intros d regs ex j. unfold decL_E. replace (47 + j)%nat with (32 + 15 + j)%nat by lia.
rewrite <- Nat.add_assoc. rewrite ew_Ereg_extra. reflexivity.
Qed.
Lemma decL_E_reg : forall d regs ex (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (decL_E d regs ex) n = getr regs r.
Proof. intros d regs ex n r H. unfold decL_E. apply ew_Ereg_nat. exact H. Qed.

(* ---- the journal at the cut, seen from the cut itself: window [sp - 112, sp) of the frame (sp the entry sp) ---- *)
Lemma decL_self_journal : forall d lyc Sc Wc Uc memc mdc k,
  dec_entry_ok B d -> dec_J B d lyc Sc Wc Uc memc mdc k -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B DEC_F (d_sp d) [] lyc Sc Wc (unpoison Uc memc) mdc [] lyc Sc Wc (unpoison Uc memc) mdc 0.
Proof.
intros d lyc Sc Wc Uc memc mdc k HE HJ HARU.
assert (HSTK : 112 + STK_RT_STR <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (HSTR : 0 <= STK_RT_STR) by (vm_compute; discriminate).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hsp16 & _ & _ & _).
assert (Hspot : d_sp d <= d_ot d).
{ unfold d_sp. destruct HPL as [(_ & H1 & H2 & _) | (_ & H1 & _)]; lia. }
unfold dec_J, d_STKJ in HJ.
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & Hhi & Hblk & Himg & Hfr & Hrem & Hpres & Hstk & Hext
  & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Ha. apply Hpres. unfold DEC_F in Ha. lia. }
split.
{ unfold astk_ok, ly_bot, DEC_F in *. rewrite Etop, Eslo, Eshi.
  split; [exact Hsp16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; lia. }
split; [intros; reflexivity | exact HQT].
Qed.

(* ---- the frame chunks from the frame facts ---- *)
Ltac decL_cs1 HF j :=
  let r := eval vm_compute in (nth j dec_saved 0%bv) in
  lazymatch goal with |- YP09.chunk_ok _ (decL_E ?d _ _) _ _ _ =>
  apply (chunk_ok_val tfibsegs _ _ _ _ 8 _ (bv_unsigned (getr (d_regs d) r))) end;
  [ rewrite fsw_SOff0;
    lazymatch goal with |- ew _ ?n = _ =>
      let m := eval vm_compute in (n - 32)%nat in
      replace n with (32 + m)%nat by reflexivity end;
    unfold decL_E; rewrite ew_Ereg_extra; cbn; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [Z.of_N]; apply u64_range | cbn [Z.of_N]; lia
  | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add];
    lazymatch goal with |- val_mem _ _ (?b + ?o) _ _ =>
      replace (b + o) with (b + 8 + 8 * Z.of_nat j) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end;
    exact (HF j%nat r eq_refl) ].
Lemma decL_cs_ok : forall d regs ex (W : world tfibsegs) mem,
  dec_frame_ok W mem (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot W mem (d_sp d - DEC_F) (d_lenp d) ->
  0 <= d_lenp d < 2 ^ 64 ->
  Forall (YP09.chunk_ok tfibsegs (decL_E d regs ex) (mrestrict (w_H W) mem) (d_sp d - DEC_F)) decL_cs.
Proof.
intros d regs ex W mem HF HL Hl.
unfold decL_cs.
constructor.
{ apply (chunk_ok_val tfibsegs _ _ _ 0 8 (SOff 33 0) (d_lenp d));
    [rewrite fsw_SOff0, decL_E_lenp; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | rewrite Z.add_0_r; exact HL]. }
constructor; [decL_cs1 HF 0%nat|]. constructor; [decL_cs1 HF 1%nat|]. constructor; [decL_cs1 HF 2%nat|].
constructor; [decL_cs1 HF 3%nat|]. constructor; [decL_cs1 HF 4%nat|]. constructor; [decL_cs1 HF 5%nat|].
constructor; [decL_cs1 HF 6%nat|]. constructor; [decL_cs1 HF 7%nat|]. constructor; [decL_cs1 HF 8%nat|].
constructor; [decL_cs1 HF 9%nat|]. constructor; [decL_cs1 HF 10%nat|]. constructor; [decL_cs1 HF 11%nat|].
constructor; [decL_cs1 HF 12%nat|]. constructor.
Qed.

(* ---- where lenp lies: the caller's real stack [sp, ot) or 8 bytes of a live fake frame (below alloc_ceiling) ---- *)
Lemma decL_lenp_range : forall d, dec_entry_ok B d ->
  4096 <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  ((d_FP d = FS_PSTAT_FP /\ d_sp d <= d_lenp d /\ d_lenp d + 8 <= d_ot d) \/
   (d_FP d = FS_PSTAT_FP ++ [(d_lenp d, d_lenp d + 8)] /\ d_ot d = d_sp d /\ d_lenp d + 8 <= alloc_ceiling)).
Proof.
intros d HE.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & _ & _).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (proj1 (proj1 (proj1 HPRE))) as HAR.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (_ & Hsp1 & Hsp2 & _).
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
destruct HPL as [(HFP & H1 & H2 & H3 & H4 & _) | (HFP & Hot & (cid & pos & Hin & Hr) & _)].
- assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
  unfold d_sp. split; [lia|]. split; [lia|]. left. split; [exact HFP | lia].
- destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & _).
  pose proof (Hr (d_lenp d) ltac:(lia)) as R0. pose proof (Hr (d_lenp d + 7) ltac:(lia)) as R7.
  unfold in_zr, frame_rng in R0, R7. cbn [fst snd] in R0, R7.
  split; [lia|]. split; [lia|]. right. unfold d_sp. split; [exact HFP|]. split; [exact Hot | lia].
Qed.

(* ---- the generic builder: the canonical state fss_retT pc 112 decL_cs rs gf at any cut with the loop's journal, ARU,
   sp and frame (FSW_rres fsw_resume_after_rtU_args_chunks over the cut's own journal decL_self_journal) ---- *)
Lemma decL_build : forall d Wc lyc Sc Uc regsc memc mdc k ex pc rs gf,
  dec_entry_ok B d -> dec_J B d lyc Sc Wc Uc memc mdc k -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = d_sp d - DEC_F ->
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) ->
  regions_wf (fsT_ret_regions DEC_F decL_cs rs) = true ->
  Forall (region_ok tfibsegs (decL_E d regsc ex) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (decL_E d regsc ex) (fsT_ret_regions DEC_F decL_cs rs) ->
  atoms_ok (decL_E d regsc ex) gf ->
  st_ok tfibsegs (decL_E d regsc ex) (fss_retT pc DEC_F decL_cs rs gf)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros d Wc lyc Sc Uc regsc memc mdc k ex pc rs gf HE HJ HARU Hsp HF HL Hwf Hrs Hpd Hgf.
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
unfold decL_E in *.
apply (fsw_resume_after_rtU_args_chunks B DEC_F (d_sp d) [] lyc Sc Wc (unpoison Uc memc) mdc [] lyc Sc Uc Wc memc mdc 0
  regsc DEC_F (decL_xs d ++ ex) decL_cs rs gf pc (proj1 HSS) (proj2 HSS)).
- exact (decL_self_journal d lyc Sc Wc Uc memc mdc k HE HJ HARU).
- exact HARU.
- exact Hsp.
- unfold DEC_F; lia.
- lia.
- reflexivity.
- exact Hwf.
- exact (decL_cs_ok d regsc ex Wc memc HF HL ltac:(lia)).
- exact Hrs.
- exact Hpd.
- exact Hgf.
Qed.

(* ==== reading a cut back from the engine's state ==== *)
(* a register the engine left as SOff n z, worth v + z *)
Lemma decL_soff : forall E n z v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 (v + z).
Proof.
intros E n z v Hn Hv Hz. apply bv_eq. rewrite denot_SOff, Hn. unfold w64.
rewrite (wz v Hv), (wz (v + z) Hz). apply zcanon_id. unfold M64. lia.
Qed.
Lemma decL_reg : forall (H : word -> bool) E ss ms (r : bv 5) e w,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof. intros H E ss ms r e w HS He Hw. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), He. exact Hw. Qed.

(* the frame words of a cut, read back from the frame region of any later engine state (its chunks unchanged) *)
Lemma decL_frame_back : forall d regs0 ex (W : world tfibsegs) ms Ex ss,
  st_ok tfibsegs Ex ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret DEC_F decL_cs) ->
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F ->
  (forall n, (33 <= n < 47)%nat -> ew Ex n = ew (decL_E d regs0 ex) n) ->
  0 <= d_lenp d < 2 ^ 64 ->
  dec_frame_ok W (ms_mem ms) (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot W (ms_mem ms) (d_sp d - DEC_F) (d_lenp d).
Proof.
intros d regs0 ex W ms Ex ss HS Hnth E2 HEx Hl.
pose proof (fsw_region_nth Ex ss (restrict (w_H W) ms) 0 _ HS Hnth) as HR.
cbn [ms_mem restrict] in HR. unfold fstk_ret in HR.
split.
- intros j r Hj.
  unfold dec_saved in Hj.
  do 13 (destruct j as [|j]; [cbn [nth_error] in Hj; inversion Hj; subst r; clear Hj;
    lazymatch goal with |- val_mem _ _ (?b + 8 + 8 * Z.of_nat ?jj) _ _ =>
      let off := eval vm_compute in (8 + 8 * Z.of_nat jj) in
      let n := eval vm_compute in (34 + jj)%nat in
      replace (b + 8 + 8 * Z.of_nat jj) with (b + off) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      apply (fsw_field Ex _ 2 b decL_cs 0 DEC_F 0 DEC_F off 8 (SOff n 0) _ HR E2);
      [ cbv [decL_cs In]; tauto
      | rewrite fsw_SOff0, (HEx n ltac:(lia)); unfold decL_E;
        replace n with (32 + (n - 32))%nat by reflexivity; rewrite ew_Ereg_extra; cbn;
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | apply u64_range | cbn; lia ]
    end|]).
  destruct j; cbn [nth_error] in Hj; discriminate Hj.
- unfold dec_lenp_slot. rewrite <- (Z.add_0_r (d_sp d - DEC_F)).
  apply (fsw_field Ex _ 2 (d_sp d - DEC_F) decL_cs 0 DEC_F 0 DEC_F 0 8 (SOff 33 0) _ HR E2);
    [ cbv [decL_cs In]; tauto
    | rewrite fsw_SOff0, (HEx 33%nat ltac:(lia)), decL_E_lenp; reflexivity
    | exact Hl | cbn; lia ].
Qed.

(* ==== re-assembling a cut ==== *)
(* the loop head from the facts a cut carries: the journal, ARU and the memory facts at the new memory, the frame
   words read back, the registers of the next head, the model facts *)
Lemma decL_mk_head : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i' six' pad' acc' regs' mem' md',
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  dec_J B d lyc Sc Wc Uc mem' md' k -> ARU tfibsegs B lyc Sc Uc Wc mem' md' ->
  decL_memf d q six' Wc lyc Sc mem' ->
  dec_frame_ok Wc mem' (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem' (d_sp d - DEC_F) (d_lenp d) ->
  spZ regs' = d_sp d - DEC_F -> getr regs' 3 = getr (d_regs d) 3 -> getr regs' 4 = getr (d_regs d) 4 ->
  getr regs' 8 = w64 DEC_WSMASK -> getr regs' 9 = w64 q ->
  getr regs' 18 = w64 (d_text d + Z.of_nat i') -> getr regs' 19 = w64 G_B64 ->
  getr regs' 20 = w64 (d_text d + Z.of_nat i') -> getr regs' 21 = w64 SHADOW_OFF ->
  getr regs' 22 = w64 (Z.of_nat (length (WriterSpec.six_bytes six'))) -> getr regs' 23 = w64 acc' -> 0 <= acc' < 2 ^ 64 ->
  getr regs' 24 = w64 (6 * Z.of_nat (length six') mod 8) -> getr regs' 25 = w64 61 -> getr regs' 26 = w64 pad' ->
  getr regs' 27 = w64 2 ->
  (i' <= length (d_tb d))%nat -> 0 <= pad' <= Z.of_nat i' -> (length six' <= i')%nat ->
  Forall (fun x => 0 <= x < 64) six' -> acc' mod 64 = last six' 0 ->
  WriterSpec.b64_dec (d_tb d) =
    match WriterSpec.b64_scan pad' six' (skipn i' (d_tb d)) with
    | Some (six'', pad'') => if (pad'' <=? 2) && WriterSpec.six_tail_ok six'' then Some (WriterSpec.six_bytes six'') else None
    | None => None
    end ->
  dec_head B d q i' six' pad' acc' Wc lyc Sc Uc regs' mem' md' k.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i' six' pad' acc' regs' mem' md'
  HH HJ HARU (Hrb & Hra & Hglob & HKe & HZb) HFr HLs Hsp R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 Hacc R24 R25 R26 R27
  Hi Hpad Hsix Hsix64 Hlast Hscan.
unfold dec_head in HH |- *. cbv zeta in HH |- *.
destruct HH as (_ & _ & Hk & HUc & Hheads & Hbl & Hq & _ & _ & Hcf & _).
repeat (split; [assumption|]). exact Hscan.
Qed.

(* the call of fuzz_free on a refused text, from a later engine state at A_fuzz_free *)
Lemma decL_free : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md',
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = A_fuzz_free ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  decL_memf d q six Wc lyc Sc (ms_mem ms) ->
  dec_frame_ok Wc (ms_mem ms) (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc (ms_mem ms) (d_sp d - DEC_F) (d_lenp d) ->
  getr (ms_regs ms) 10 = w64 q -> getr (ms_regs ms) 1 = w64 DEC_RA_FREE -> spZ (ms_regs ms) = d_sp d - DEC_F ->
  getr (ms_regs ms) 3 = getr (d_regs d) 3 -> getr (ms_regs ms) 4 = getr (d_regs d) 4 ->
  getr (ms_regs ms) 8 = w64 DEC_WSMASK ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HH HFREE HS Hrv Hpc HJ HARU
  (Hrb & Hra & Hglob & HKe & HZb) HFr HLs R10 R1 Hsp R3 R4 R8 Hdec.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
apply (HFREE Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
unfold dec_head in HH. cbv zeta in HH.
destruct HH as (_ & _ & Hk & HUc & Hheads & Hbl & Hq & _ & _ & Hcf & _).
unfold dec_at_free.
repeat (split; [assumption|]). exact HKe.
Qed.
End L0.
