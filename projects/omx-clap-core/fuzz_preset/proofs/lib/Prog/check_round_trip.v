From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes WriterSpec
WriterValue WriterApp WriterRet TxCalls TxRet PjWriteHyp round_trip_text_c pj_string_c pj_set_c pj_parse_c
parse_noting_c pj_free_c fuzz_free_c strlen_c strcmp_c same_c memset_c fuzz_alloc_ran_out_c check_round_trip_c
check_round_trip_seg check_round_trip_loop check_round_trip_m check_round_trip_g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require RttModel PjSame GIInit.
Import ListNotations.
Local Open Scope Z_scope.

(* check_round_trip of #102 (fuzz_preset.c:772-781, round_trip_rewrite inlined) in the plain twin
   pau-preset-102 fuzz_preset.plain (sha256 c8f4d6b8e567b0b1...), 0x13fe4 size 680.  The walk goes backwards from the
   epilogue (st9) to the entry (st0).  ro / oo are the entry bytes of g_ran_out / g_own_ran_out: no allocation is
   refused under the rooms premises, so the bytes keep their values (gi_flags, from the cstep frame and
   globals_free omx_G); round_trip_text (doc, 0, &copy) returns 1 when one of them is nonzero (st1o: the copy, still
   empty, is freed and 1 returned), else every out_of_memory() test of the rewrite reads two zero bytes. *)
(* Two facts of the write and read models, proved as in RttStgCmp.v (rf_trace, rf_wcalls and their helpers), so
   that this walk does not depend on the round_trip_text stage walks. *)
Lemma crt_rf_trace : forall x ok cnt fail res tr, jr_run jr_strtod x ok = (res, tr) ->
  oks ok cnt fail (calls tr) -> cnt + Z.of_nat (calls tr) <= fail ->
  res = json_read jr_strtod x /\ tr = snd (jr_run jr_strtod x []).
Proof.
  intros x ok cnt fail res tr HR HO HF.
  destruct (ok_upto_dec ok (ncalls jr_strtod x)) as [Hu | (j & Hj & Hf & Hu)].
  - rewrite (G7_1 jr_strtod x ok Hu) in HR. injection HR as <- <-. split; reflexivity.
  - exfalso. destruct (G7_2 jr_strtod x ok j Hj Hf Hu) as [_ HC]. rewrite HR in HC. cbn [snd] in HC.
    rewrite HC in HO, HF. specialize (HO j ltac:(lia)). rewrite Hf in HO.
    destruct (Z.eqb_spec (cnt + Z.of_nat j) fail); [lia | cbn in HO; discriminate HO].
Qed.

Lemma crt_dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma crt_dbl_le : forall f c need, 0 < c -> dbl f c need <= Z.max c (2 * need).
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma crt_dbl_S : forall f c need, c < need -> dbl (S f) c need = dbl f (2 * c) need.
Proof. intros f c need H. cbn [dbl]. destruct (Z.leb_spec need c) as [H'|H']; [lia | reflexivity]. Qed.

Lemma crt_newcap : forall c need, (c = 0 \/ 4096 <= c) -> c < need ->
  c + 4096 <= newcap c need /\ newcap c need <= Z.max 4096 (2 * need).
Proof.
  intros c need Hc Hn. unfold newcap.
  destruct (Z.eqb_spec c 0) as [->|H0]; cbv beta iota.
  - pose proof (crt_dbl_ge 64 4096 need ltac:(lia)). pose proof (crt_dbl_le 64 4096 need ltac:(lia)). lia.
  - destruct Hc as [Hc|Hc]; [contradiction|]. rewrite (crt_dbl_S 63 c need Hn).
    pose proof (crt_dbl_ge 63 (2 * c) need ltac:(lia)). pose proof (crt_dbl_le 63 (2 * c) need ltac:(lia)). lia.
Qed.

Lemma crt_zsum_nn : forall ls, Forall (fun l => 0 <= l) ls -> 0 <= zsum ls.
Proof. intros ls H. induction H as [|l ls Hl _ IH]; cbn [zsum]; lia. Qed.

Lemma crt_gc : forall ls x c M, (c = 0 \/ 4096 <= c) -> Forall (fun l => 0 <= l) ls -> x + zsum ls + 1 <= M ->
  c + 4096 * Z.of_nat (length (grow_calls x c ls)) <= Z.max c (Z.max 4096 (2 * M)).
Proof.
  induction ls as [|l ls IH]; intros x c M Hc Hl HM; cbn [grow_calls length zsum] in *.
  - lia.
  - apply Forall_cons_iff in Hl. destruct Hl as [Hl0 Hls]. pose proof (crt_zsum_nn ls Hls) as Z0.
    destruct (Z.ltb_spec c (x + l + 1)) as [H|H]; cbn [length].
    + destruct (crt_newcap c (x + l + 1) Hc H) as [N1 N2].
      pose proof (IH (x + l) (newcap c (x + l + 1)) M ltac:(right; lia) Hls ltac:(lia)) as IH'. lia.
    + pose proof (IH (x + l) c M Hc Hls ltac:(lia)) as IH'. lia.
Qed.

Lemma crt_rf_wcalls : forall t p, 4096 * wcalls t p <= Z.max 4096 (2 * (wlen t p + 1)).
Proof.
  intros t p. unfold wcalls.
  assert (HF : Forall (fun l => 0 <= l) (piece_lens (wdpieces t p))).
  { apply Forall_forall. intros l Hl. unfold piece_lens in Hl. apply in_map_iff in Hl. destruct Hl as (b & <- & _). lia. }
  assert (HZ : zsum (piece_lens (wdpieces t p)) = wlen t p).
  { change (piece_lens (wdpieces t p)) with (plen (wdpieces t p)). rewrite zsum_plen. reflexivity. }
  pose proof (crt_gc (piece_lens (wdpieces t p)) 0 0 (wlen t p + 1) (or_introl eq_refl) HF ltac:(lia)) as H.
  lia.
Qed.

Ltac crt_cs tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Ltac crl := unfold CRT_K in *; lia.

Lemma crt_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. apply unsigned_lit. exact H. Qed.

Section Main.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Hypothesis HSEG : ms_segs B = rsegs.

Context {fx0 : YK11.FPState}.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (Lam0 : list (Z * Z)) (peak0 cnt0 : Z) (b0 : rf_R F) (doc : Z) (t : jv) (D : list (Z * Z)) (x : list Z).
Hypothesis HRE : @reader_env fx0 rc B API CRT_K L0 A0 regs0 mem0 md0.
Hypothesis HI0 : st_init_done A0 = true.
Hypothesis HL0 : ledger B L0 A0 mem0 Lam0 peak0 cnt0 (2 ^ 64 - 1).
Hypothesis HC0 : cnt0 < 2 ^ 62 - 2 ^ 30.
Hypothesis HB0 : rf_ok F A0 b0.
Hypothesis HA0 : getr regs0 10 = Z_to_bv 64 doc.
Hypothesis HN0 : pj_node segs mem0 (lin Lam0) doc t D.
Hypothesis HD0 : forall bk, In bk D -> In bk Lam0.
Hypothesis HSD : spZ regs0 <= doc.
Hypothesis HX : json_read jr_strtod x = Some t.
Hypothesis HXL : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HW0 : wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HW1 : wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HRM1 : rtt_rooms F b0 cnt0 t false.
Hypothesis HRM2 : rtt_rooms F (crt_b1 F b0 cnt0 t) (crt_cnt1 cnt0 t) t true.
Hypothesis HOBJ : forall ms, t = JObj ms -> forall Df, crt_dl (PjRoundTrip.ttrace t) Df ->
  crt_obj_rooms F (crt_b2 F b0 cnt0 t Df) (crt_cnt2 cnt0 t) t (Z.of_nat (length ms)).
Variables (ro oo : Z).
Hypothesis HRO : 0 <= ro < 256.
Hypothesis HOO : 0 <= oo < 256.
Hypothesis HFR0 : Mem.bytes_at segs mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)).
Hypothesis HFO0 : Mem.bytes_at segs mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)).
Hypothesis HGF : globals_free B API GIInit.omx_G.

Let SP := spZ regs0.
Let SQ := SP - 256.

Definition cells0 : list cell :=
  crt_cells (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
    (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (getr regs0 25).

Definition cpost (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' (Lam' : list (Z * Z)) (peak' cset : Z) (b' : rf_R F),
    c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ fregs_kept fx0 fx' /\
    rtt_rel B API CRT_K regs0 alloc_statics L0 A0 mem0 md0 L' A' regs' mem' md' /\
    rd_cells B mem' /\ st_init_done A' = true /\
    Mem.bytes_at segs mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
    Mem.bytes_at segs mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) /\
    ( (ro <> 0 \/ oo <> 0) /\ getr regs' 10 = Z_to_bv 64 1 /\
      ledger B L' A' mem' Lam' peak' (cnt0 + wcalls t false) (2 ^ 64 - 1) /\
      peak0 <= peak' /\ Permutation Lam' Lam0 /\
      rf_ok F A' (rtt_bo F b0 cnt0 t false) /\
      pj_node segs mem' (lin Lam') doc t D
    \/
      ro = 0 /\ oo = 0 /\ getr regs' 10 = Z_to_bv 64 0 /\
      0 <= cset <= 3 /\ (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) /\
      ledger B L' A' mem' Lam' peak' (cnt0 + crt_count t cset) (2 ^ 64 - 1) /\
      peak0 <= peak' /\ Permutation Lam' Lam0 /\
      rf_ok F A' b' /\ crt_fin F b0 cnt0 t cset b' /\
      pj_node segs mem' (lin Lam') doc t D).

Definition gi (fx : YK11.FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (New : list (Z * Z)) : Prop :=
  cstep B API SP CRT_K alloc_statics NoG L0 A0 mem0 md0 L A mem md /\
  ro_agree segs mem /\ st_init_done A = true /\
  frm_zero (@fp_csr fx) /\ fregs_kept fx0 fx /\
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) /\ peak0 <= peak /\
  Permutation Lam (New ++ Lam0) /\ new_blks L0 A0 New /\
  rf_ok F A b /\
  rw_cells segs mem (SP - 88) cells0 /\
  pj_node segs mem (lin Lam) doc t D.

Lemma crt_env : alloc_ceiling + CRT_K <= SP /\ SP <= 2 ^ 47 /\ SP mod 16 = 0 /\
  getr regs0 2 = Z_to_bv 64 SP /\ YK0s.ret_ok (getr regs0 1) /\ getr regs0 4 = Z_to_bv 64 (ms_tp B) /\
  strtod_c.STRTOD_GLOBALS_TOP <= SP - CRT_K.
Proof.
  destruct HRE as (_ & _ & _ & _ & _ & (_ & _ & _ & Hra & Hal & Hlo & _ & _ & Htp & _) & H47 & Hgt & _).
  unfold SP. split; [exact Hlo|]. split; [exact H47|]. split; [exact Hal|].
  split; [unfold spZ; symmetry; apply Step.Z_to_bv_lit_self|]. split; [exact Hra|]. split; [exact Htp | exact Hgt].
Qed.

Lemma crt_sp : 140735332483072 + 14064 <= SP <= 2 ^ 47 /\ SP mod 16 = 0 /\ SQ = SP - 256 /\
  alloc_ceiling + 14064 <= SP.
Proof.
  destruct crt_env as (Hce & H47 & H16 & _). pose proof alloc_ceiling_value as Hc. unfold CRT_K in Hce.
  split; [lia|]. split; [exact H16|]. split; [reflexivity | exact Hce].
Qed.

Lemma crt_static : ms_tp B = strtod_c.STRTOD_TP /\ errno_addr B = strtod_c.STRTOD_ERRNO /\
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD /\ ms_guard B = strtod_c.STRTOD_GUARD.
Proof. destruct HRE as (_ & H1 & H2 & H3 & H4 & _). auto. Qed.

Lemma crt_doc : SP <= doc /\ doc + 56 <= 2 ^ 64.
Proof.
  split; [exact HSD|].
  assert (H : exists ty num str kids keys n cap, pj_hdr segs mem0 doc ty num str kids keys n cap).
  { pose proof HN0 as HN. destruct t; cbn [pj_node] in HN;
      destruct HN as (_ & _ & num & str & kids & keys & n & cap & Hh & _); do 7 eexists; exact Hh. }
  destruct H as (ty & num & str & kids & keys & n & cap & Hh). destruct Hh as [[_ [_ [H2 _]]] _]. exact H2.
Qed.

Lemma crt_statics_img : forall a, alloc_statics a -> in_img B a.
Proof.
  intros a Ha. unfold in_img. rewrite HSEG.
  split; [intros E; apply (f_equal (@length Segment)) in E; vm_compute in E; discriminate E|].
  assert (C1 : existsb (fun r => (bv_unsigned (fst r) <=? G_LIVE) &&
                 (G_LIVE + 24 <=? bv_unsigned (fst r) + bv_unsigned (snd r))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  assert (C2 : existsb (fun r => (bv_unsigned (fst r) <=? G_FAIL) &&
                 (G_FAIL + 8 <=? bv_unsigned (fst r) + bv_unsigned (snd r))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C1 as (r1 & H1 & E1). apply existsb_exists in C2 as (r2 & H2 & E2).
  apply andb_prop in E1 as [E1 F1]. apply andb_prop in E2 as [E2 F2]. apply Z.leb_le in E1, F1, E2, F2.
  unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [exists r1 | exists r1 | exists r1 | exists r2]; (split; [assumption | lia]).
Qed.

Definition nblk (New : list (Z * Z)) (a : Z) : Prop := exists ba bk, In (ba, bk) New /\ ba - 16 <= a < ba + bk.

Lemma nblk_facts : forall L A mem md Lam peak cnt fail New a, MR L A mem md -> ledger B L A mem Lam peak cnt fail ->
  (forall bk, In bk New -> In bk Lam) -> nblk New a ->
  exists ba bk, In (ba, bk) New /\ ba - 16 <= a < ba + bk /\ In (ba - 16, bk + 16) (blocks L A) /\
    4112 <= ba /\ ba + bk <= alloc_ceiling /\ ~ in_img B a.
Proof.
  intros L A mem md Lam peak cnt fail New a HM HL HS (ba & bk & Hin & Ha).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF (ba, bk) (HS _ Hin)) as (Hk & Hb & _ & Hi). cbn [fst snd] in *.
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail ba bk HM HL (HS _ Hin)) as (R1 & R2 & _).
  exists ba, bk. split; [exact Hin|]. split; [exact Ha|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
  replace a with (ba - 16 + (a - (ba - 16))) by lia. apply Hi. lia.
Qed.

Lemma crt_renv : forall fx L A mem md Lam peak cnt b New regs K,
  gi fx L A mem md Lam peak cnt b New ->
  getr regs 2 = Z_to_bv 64 (SP - 256) -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  0 <= K <= CRT_K - 256 ->
  @reader_env fx rc B API K L A regs mem md.
Proof.
  intros fx L A mem md Lam peak cnt b New regs K (HC & Hro & Hin & Hfz & _) G2 G4 Hra HK.
  destruct HRE as (S1 & S2 & S3 & S4 & S5 & _).
  destruct crt_env as (_ & _ & _ & _ & _ & Htp & Hgt).
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2).
  pose proof HC as (HM & HW & HB & _ & _ & _ & _ & _ & _ & HS).
  assert (Hs : spZ regs = SP - 256) by (unfold spZ; rewrite G2; apply crt_uns; lia).
  unfold CRT_K in *.
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|].
  split.
  { split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
    split; [rewrite Hs; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
    split; [intros a Ha; apply HS; left; lia|].
    split; [rewrite G4; exact Htp|].
    split; [intros a Ha; apply HS; right; exact Ha|].
    intros Hd. rewrite Hin in Hd. discriminate. }
  split; [lia|]. split; [unfold strtod_c.STRTOD_GLOBALS_TOP in *; lia|]. split; [exact Hfz|].
  exact (rd_cells_of B API L A mem md AX HM Hro).
Qed.

Lemma crt_rplace : forall fx L A mem md Lam peak cnt b New regs p,
  gi fx L A mem md Lam peak cnt b New -> spZ regs = SP - 256 -> SP - 256 <= p -> p + 56 <= SP ->
  rplace B L A Lam regs mem p.
Proof.
  intros fx L A mem md Lam peak cnt b New regs p (HC & _ & Hin & _) Hs Hp1 Hp2.
  pose proof HC as (HM & _).
  destruct crt_static as (_ & Herr & _). destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof alloc_ceiling_value as Hc.
  split; [left; split; lia|].
  split; [intros _ Hd; rewrite Hin in Hd; discriminate|].
  intros i Hi. split; [intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia|].
  split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|].
  split; [rewrite Herr; unfold strtod_c.STRTOD_ERRNO; lia|].
  intro Him. destruct (crt_img_low B HSEG) as [HI _]. pose proof (HI _ Him). lia.
Qed.

Lemma gi_step : forall fx fx' L A mem md Lam peak cnt b New sp2 K2 E2 G2 L' A' mem' md' Lam' peak' cnt' b'
    New',
  gi fx L A mem md Lam peak cnt b New ->
  cstep B API sp2 K2 E2 G2 L A mem md L' A' mem' md' ->
  SP - CRT_K <= sp2 - K2 -> sp2 <= SP - 256 ->
  (forall a, E2 a -> (SP - 256 <= a < SP - 88) \/ alloc_statics a \/ nblk New a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> ~ G2 a k) ->
  (forall a, SP - 256 <= a < SP - 88 -> E2 a \/ ~ E2 a) ->
  (forall a, SP - 256 <= a < SP - 88 -> E2 a -> writable_at segs mem' a) ->
  ro_agree segs mem' -> st_init_done A' = true -> frm_zero (@fp_csr fx') -> fregs_kept fx0 fx' ->
  ledger B L' A' mem' Lam' peak' cnt' (2 ^ 64 - 1) -> peak <= peak' ->
  Permutation Lam' (New' ++ Lam0) -> new_blks L0 A0 New' ->
  rf_ok F A' b' ->
  gi fx' L' A' mem' md' Lam' peak' cnt' b' New'.
Proof.
  intros fx fx' L A mem md Lam peak cnt b New sp2 K2 E2 G2 L' A' mem' md' Lam' peak' cnt' b' New'
    (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN)
    HC2 W1 W2 HE HG HDE HEW Hro' Hin' Hfz' Hfk' HL' Hpk' HP' HNB' Hres'.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2). destruct crt_doc as (Hd1 & Hd2).
  destruct crt_static as (_ & Herr & _).
  pose proof alloc_ceiling_value as Hc. unfold CRT_K in *.
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  assert (HNS : forall bk, In bk New -> In bk Lam)
    by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb).
  assert (HDS : forall bk, In bk D -> In bk Lam)
    by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; apply HD0; exact Hb).
  assert (HDS' : forall bk, In bk D -> In bk Lam')
    by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HP')); apply in_or_app; right; apply HD0; exact Hb).
  assert (Herr' : errno_addr B + 4 <= alloc_ceiling) by (rewrite Herr; unfold strtod_c.STRTOD_ERRNO; lia).
  assert (Hst : forall a, alloc_statics a -> a < alloc_ceiling)
    by (intros a Ha; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia).
  assert (HNB2 : forall a, nblk New a -> a < alloc_ceiling /\ ~ in_img B a).
  { intros a Ha. destruct (nblk_facts L A mem md Lam peak cnt _ New a HM HL HNS Ha) as (ba & bk & _ & H1 & _ & _ & H2 & H3).
    split; [lia | exact H3]. }
  assert (HEB : forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> E2 (a + i) -> alloc_statics (a + i)).
  { intros a k i Hb Hi He. pose proof (HPers a k Hb ltac:(intros [])) as Hb1.
    pose proof Hb1 as Hb1'. unfold blocks in Hb1'. apply in_map_iff in Hb1' as ([q n] & E1 & Hq). cbn [fst snd] in E1.
    injection E1 as E1 E2'. subst n.
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq) as [R1 R2]. rewrite E1 in R1, R2.
    destruct (HE _ He) as [Hw|[Hs|Hn]]; [lia | exact Hs|].
    exfalso. destruct (nblk_facts L A mem md Lam peak cnt _ New _ HM HL HNS Hn) as (ba & bk & Hbn & H1 & H2 & _).
    assert (Hne : (a, k) <> (ba - 16, bk + 16)).
    { intros X. injection X as X1 X2. apply (HNB ba bk Hbn). rewrite <- X1, <- X2. exact Hb. }
    destruct (crt_blk_disj B API L A mem md _ _ _ _ HM Hb1 H2 Hne); lia. }
  split.
  { eapply cstep_trans; [exact HC | exact HC2 | crl | crl | crl | crl | | exact HEB | exact HG | |].
    - intros a Ha He. destruct (HE a He) as [Hw|[Hs|Hn]]; [left; crl | right; exact Hs |].
      exfalso. destruct (HNB2 a Hn) as [H1 H2]. destruct Ha as [Ha|Ha]; [crl | exact (H2 Ha)].
    - intros a Ha. destruct (Z_lt_le_dec a (SP - 256)) as [X|X]; [right|destruct (Z_lt_le_dec a (SP - 88)) as [Y|Y]].
      + intros He. destruct (HE a He) as [Hw|[Hs|Hn]]; [crl | pose proof (Hst a Hs); crl | destruct (HNB2 a Hn); crl].
      + apply HDE. crl.
      + right. intros He. destruct (HE a He) as [Hw|[Hs|Hn]]; [crl | pose proof (Hst a Hs); crl | destruct (HNB2 a Hn); crl].
    - intros a Ha He. destruct (HE a He) as [Hw|[Hs|Hn]]; [apply HEW; [crl | exact He] | pose proof (Hst a Hs); crl |].
      destruct (HNB2 a Hn); crl. }
  split; [exact Hro'|]. split; [exact Hin'|]. split; [exact Hfz'|]. split; [exact Hfk'|].
  split; [exact HL'|]. split; [lia|]. split; [exact HP'|]. split; [exact HNB'|].
  split; [exact Hres'|].
  split.
  { apply (cstep_rw B API sp2 K2 E2 G2 L A mem md L' A' mem' md'); [exact HC2 | lia | cbn; lia | | exact Hcells].
    cbn [cells0 crt_cells cells_size csize]. intros a Ha. split.
    - unfold cwin. lia.
    - intros He. destruct (HE a He) as [Hw|[Hs|Hn]]; [lia | pose proof (Hst a Hs); lia | destruct (HNB2 a Hn); lia]. }
  apply (cstep_pj_node B API sp2 K2 E2 G2 L A mem md L' A' mem' md' Lam peak cnt (2 ^ 64 - 1) doc t D (lin Lam'));
    [exact HSEG | exact (crt_img_low B HSEG) | exact HC2 | exact HL | exact HDS | exact HN | intros a k Hak; exact (HDS' _ Hak) | lia | lia | |].
  - intros a Ha. split; [unfold cwin; lia|].
    intros He. destruct (HE a He) as [Hw|[Hs|Hn]]; [lia | pose proof (Hst a Hs); lia | destruct (HNB2 a Hn); lia].
  - intros ba bk Hb. pose proof HL0 as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF (ba, bk) (HD0 _ Hb)) as (Hk & Hbl & _ & Hi). cbn [fst snd] in *.
    split; [exact (HG _ _ Hbl)|].
    intros i Hi2 He. replace (ba + i) with (ba - 16 + (i + 16)) in He by lia.
    pose proof (HEB _ _ (i + 16) Hbl ltac:(lia) He) as Hs. apply (Hi (i + 16)); [lia|].
    exact (crt_statics_img _ Hs).
Qed.

(* g_ran_out and g_own_ran_out are entries 5 and 7 of omx_G (GIInit.v, LedgerCells.GL_cells) *)
Lemma crt_gro_in : in_globals GIInit.omx_G G_RAN_OUT.
Proof.
  exists GL_RAN_OUT, 8. split; [unfold GIInit.omx_G; cbn [In]; right; right; right; right; left; reflexivity|].
  unfold G_RAN_OUT, GL_RAN_OUT. lia.
Qed.

Lemma crt_goo_in : in_globals GIInit.omx_G GL_OWN_RAN_OUT.
Proof.
  exists GL_OWN_RAN_OUT, 8. split; [unfold GIInit.omx_G; cbn [In]; right; right; right; right; right; right; left; reflexivity|].
  lia.
Qed.

(* A byte of omx_G outside alloc_statics keeps its entry value wherever gi holds: the cstep from the entry frames
   every image byte that no allocator state owns, outside the window and alloc_statics. *)
Lemma crt_flag_keep : forall a, in_globals GIInit.omx_G a -> ~ alloc_statics a ->
  forall fx L A mem md Lam peak cnt b New, gi fx L A mem md Lam peak cnt b New ->
  mbyte segs mem a = mbyte segs mem0 a.
Proof.
  intros a Hg Hs fx L A mem md Lam peak cnt b New (HC & _).
  destruct (HGF a Hg) as (Himg & Hlo & _ & Herr & Hown).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HJ & _).
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  refine (proj1 (HJ a Himg (fun L1 A1 m1 d1 H1 => proj1 (Hown L1 A1 m1 d1 H1)) _ Hs)).
  unfold cwin. intros [X|X]; [unfold CRT_K in *; lia | exact (Herr X)].
Qed.

Lemma gi_flags : forall fx L A mem md Lam peak cnt b New, gi fx L A mem md Lam peak cnt b New ->
  Mem.bytes_at segs mem G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
  Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)).
Proof.
  intros fx L A mem md Lam peak cnt b New HG.
  split.
  - apply (crt_bytes_frame segs mem0 mem _ _ HFR0). rewrite length_le1. intros i Hi.
    assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
    refine (crt_flag_keep _ crt_gro_in _ fx L A mem md Lam peak cnt b New HG).
    unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, G_RAN_OUT. lia.
  - apply (crt_bytes_frame segs mem0 mem _ _ HFO0). rewrite length_le1. intros i Hi.
    assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r.
    refine (crt_flag_keep _ crt_goo_in _ fx L A mem md Lam peak cnt b New HG).
    unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_OWN_RAN_OUT. lia.
Qed.

(* The value the call returns (s1, moved to a0 at 0x14250) and the bound with it: 1 when memory had run out, after
   round_trip_text (doc, 0, &copy) alone; 0 with crt_fin. *)
Definition carm (rv cnt : Z) (b : rf_R F) (cset : Z) : Prop :=
  (rv = 1 /\ (ro <> 0 \/ oo <> 0) /\ cnt = cnt0 + wcalls t false /\ b = rtt_bo F b0 cnt0 t false) \/
  (rv = 0 /\ ro = 0 /\ oo = 0 /\ cnt = cnt0 + crt_count t cset /\ 0 <= cset <= 3 /\
   (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) /\ crt_fin F b0 cnt0 t cset b).

Lemma st9 : forall fx L A regs mem md Lam peak cnt b cset rv,
  gi fx L A mem md Lam peak cnt b [] ->
  getr regs 2 = Z_to_bv 64 (SP - 256) -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 26 = getr regs0 26 -> getr regs 27 = getr regs0 27 ->
  getr regs 9 = Z_to_bv 64 rv -> carm rv cnt b cset ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14250) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b cset rv HG G2 G3 G4 G26 G27 G9 Harm.
  pose proof (gi_flags _ _ _ _ _ _ _ _ _ _ HG) as (HF1 & HF2).
  destruct HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & _ & Hres & Hcells & HN).
  destruct crt_env as (_ & _ & _ & Hsp0 & Hra & _ & _).
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2).
  pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (getr regs0 1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (SP - 256)) + 256)) (getr regs 3) (getr regs 4)
        (getr regs 5) (getr regs 6) (getr regs 7) (getr regs0 8) (getr regs0 9) (getr regs 9) (getr regs 11)
        (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
        (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23)
        (getr regs0 24) (getr regs0 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) /\ pc' = ret_pc (getr regs0 1) /\ mem' = mem) _ Hh Hz).
  { unfold rmk. rewrite G2. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_epi (getr regs 1) (Z_to_bv 64 (SP - 256)) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem
        (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
        (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (getr regs0 25)).
      + rewrite crt_uns by lia. lia.
      + rewrite crt_uns by lia. replace (SP - 256 + 168) with (SP - 88) by lia.
        rewrite <- HSEG. exact Hcells.
    - intros ms E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros R pc' mem' regs' (-> & -> & ->) Hg.
  rewrite crt_uns in Hg by lia. replace (SP - 256 + 256) with SP in Hg by lia.
  assert (G10' : getr regs' 10 = Z_to_bv 64 rv) by (rewrite Hg; exact G9).
  apply SR_ret. unfold cpost.
  exists fx, L, A, regs', mem, md, Lam, peak, cset, b.
  rewrite (kb_ret_pc _ Hra).
  split; [reflexivity|]. split; [exact Hfz|]. split; [exact Hfk|].
  split.
  { apply cstep_rtt; [exact HC|].
    crt_cs ltac:(rewrite Hg; first [reflexivity | exact (eq_sym Hsp0) | exact G3 | exact G4
                                    | exact G26 | exact G27]). }
  split; [exact (rd_cells_of B API L A mem md AX HM Hro)|].
  split; [exact Hin|]. split; [exact HF1|]. split; [exact HF2|].
  destruct Harm as [(-> & Hro' & Hcnt & Eb) | (-> & Er & Eo & Hcnt & Hcs & Hcs0 & Hfin)].
  - left. split; [exact Hro'|]. split; [exact G10'|].
    split; [rewrite <- Hcnt; exact HL|]. split; [exact Hpk|]. split; [exact HP|].
    split; [rewrite <- Eb; exact Hres | exact HN].
  - right. split; [exact Er|]. split; [exact Eo|]. split; [exact G10'|].
    split; [exact Hcs|]. split; [exact Hcs0|].
    split; [rewrite <- Hcnt; exact HL|]. split; [exact Hpk|]. split; [exact HP|].
    split; [exact Hres|]. split; [exact Hfin | exact HN].
Qed.


Lemma crt_nodup_l : forall {T} (l1 l2 : list T), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  intros T l1. induction l1 as [|y0 l1 IH]; intros l2 H; [apply List.NoDup_nil|].
  cbn [app] in H. pose proof (proj1 (NoDup_cons_iff y0 (l1 ++ l2)) H) as [Hn H2].
  apply List.NoDup_cons; [intros Hy; apply Hn; apply in_or_app; left; exact Hy | exact (IH l2 H2)].
Qed.

Lemma crt_nodup_mid : forall {T} (l1 l2 : list T) z0, List.NoDup (l1 ++ l2) -> In z0 l1 -> In z0 l2 -> False.
Proof.
  intros T l1. induction l1 as [|y0 l1 IH]; intros l2 z0 H H1 H2; [destruct H1|].
  cbn [app] in H. pose proof (proj1 (NoDup_cons_iff y0 (l1 ++ l2)) H) as [Hn H3].
  destruct H1 as [->|H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 z0 H3 H1 H2)].
Qed.

Lemma gi_nodup : forall fx L A mem md Lam peak cnt b New,
  gi fx L A mem md Lam peak cnt b New -> List.NoDup (map fst New).
Proof.
  intros fx L A mem md Lam peak cnt b New (_ & _ & _ & _ & _ & HL & _ & HP & _).
  destruct HL as (_ & _ & _ & _ & ND & _).
  pose proof (Permutation_map fst HP) as HPm. rewrite map_app in HPm.
  exact (crt_nodup_l _ _ (Permutation_NoDup HPm (proj1 (NoDup_ListNoDup _) ND))).
Qed.

Lemma gi_sub : forall fx L A mem md Lam peak cnt b New bk,
  gi fx L A mem md Lam peak cnt b New -> In bk New -> In bk Lam.
Proof.
  intros fx L A mem md Lam peak cnt b New bk (_ & _ & _ & _ & _ & _ & _ & HP & _) Hb.
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hb.
Qed.

Lemma gi_blk_sep : forall fx L A mem md Lam peak cnt b New1 New2 a k y,
  gi fx L A mem md Lam peak cnt b (New1 ++ New2) -> In (a, k) New2 -> a - 16 <= y < a + k -> ~ blk_set New1 y.
Proof.
  intros fx L A mem md Lam peak cnt b New1 New2 a k y HG Hin Hx (a' & k' & Hin' & Hx').
  pose proof (gi_nodup _ _ _ _ _ _ _ _ _ _ HG) as ND. rewrite map_app in ND.
  pose proof HG as (HC & _ & _ & _ & _ & HL & _).
  pose proof HC as (HM & _).
  destruct (Z.eq_dec a a') as [E|E].
  - subst a'. exact (crt_nodup_mid _ _ a ND (in_map fst _ _ Hin') (in_map fst _ _ Hin)).
  - pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
    destruct (HF (a, k) (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG (in_or_app _ _ _ (or_intror Hin)))) as (_ & Hb & _).
    destruct (HF (a', k') (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG (in_or_app _ _ _ (or_introl Hin')))) as (_ & Hb' & _).
    cbn [fst snd] in Hb, Hb'.
    assert (Hne : (a - 16, k + 16) <> (a' - 16, k' + 16)) by (intros X; injection X; lia).
    destruct (crt_blk_disj B API L A mem md _ _ _ _ HM Hb Hb' Hne); lia.
Qed.

Lemma gi_node : forall fx L A mem md Lam peak cnt b New sp2 K2 E2 G2 L' A' mem' md' Lam' p tc Dc,
  gi fx L A mem md Lam peak cnt b New ->
  cstep B API sp2 K2 E2 G2 L A mem md L' A' mem' md' ->
  pj_node segs mem (lin Lam) p tc Dc -> (forall bk, In bk Dc -> In bk New) -> (forall bk, In bk Dc -> In bk Lam') ->
  SP - 256 <= p -> p + 56 <= SP - 88 ->
  (forall a, p <= a < p + 56 -> ~ cwin B sp2 K2 a /\ ~ E2 a) ->
  (forall a k, In (a, k) Dc -> ~ G2 (a - 16) (k + 16) /\ forall i, 0 <= i < k -> ~ E2 (a + i)) ->
  pj_node segs mem' (lin Lam') p tc Dc.
Proof.
  intros fx L A mem md Lam peak cnt b New sp2 K2 E2 G2 L' A' mem' md' Lam' p tc Dc HG HC2 HN HDN HDL Hp1 Hp2 HP HD.
  pose proof HG as (_ & _ & _ & _ & _ & HL & _).
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  apply (cstep_pj_node B API sp2 K2 E2 G2 L A mem md L' A' mem' md' Lam peak cnt (2 ^ 64 - 1) p tc Dc (lin Lam'));
    [exact HSEG | exact (crt_img_low B HSEG) | exact HC2 | exact HL | | exact HN | | lia | lia | exact HP | exact HD].
  - intros bk Hb. exact (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG (HDN bk Hb)).
  - intros a k Hak. exact (HDL _ Hak).
Qed.

Lemma gi_blk_stat : forall fx L A mem md Lam peak cnt b New a k i,
  gi fx L A mem md Lam peak cnt b New -> In (a, k) New -> 0 <= i < k ->
  ~ alloc_statics (a + i) /\ a + i < alloc_ceiling /\ 4096 <= a + i.
Proof.
  intros fx L A mem md Lam peak cnt b New a k i HG Hin Hi.
  pose proof HG as (HC & _ & _ & _ & _ & HL & _). pose proof HC as (HM & _).
  assert (Hnb : nblk New (a + i)) by (exists a, k; split; [exact Hin | lia]).
  destruct (nblk_facts L A mem md Lam peak cnt _ New (a + i) HM HL (fun bk H => gi_sub _ _ _ _ _ _ _ _ _ _ _ HG H) Hnb)
    as (ba & bk & Hb & Hr & _ & H1 & H2 & H3).
  split; [intros Hs; exact (H3 (crt_statics_img _ Hs))|]. lia.
Qed.

Lemma gi_sep2 : forall fx L A mem md Lam peak cnt b New a k a' k' y,
  gi fx L A mem md Lam peak cnt b New -> In (a, k) New -> In (a', k') New -> a <> a' ->
  a - 16 <= y < a + k -> a' - 16 <= y < a' + k' -> False.
Proof.
  intros fx L A mem md Lam peak cnt b New a k a' k' y HG Hin Hin' E Hy Hy'.
  pose proof HG as (HC & _ & _ & _ & _ & HL & _). pose proof HC as (HM & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF (a, k) (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG Hin)) as (_ & Hb & _).
  destruct (HF (a', k') (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG Hin')) as (_ & Hb' & _).
  cbn [fst snd] in Hb, Hb'.
  assert (Hne : (a - 16, k + 16) <> (a' - 16, k' + 16)) by (intros X; injection X; lia).
  destruct (crt_blk_disj B API L A mem md _ _ _ _ HM Hb Hb' Hne); lia.
Qed.

Lemma gi_fst_ne : forall fx L A mem md Lam peak cnt b N1 N2 q c a k,
  gi fx L A mem md Lam peak cnt b (N1 ++ (q, c) :: N2) -> In (a, k) (N1 ++ N2) -> a <> q.
Proof.
  intros fx L A mem md Lam peak cnt b N1 N2 q c a k HG Hin E. subst a.
  pose proof (gi_nodup _ _ _ _ _ _ _ _ _ _ HG) as ND.
  pose proof (Permutation_map fst (Permutation_sym (Permutation_middle N1 N2 (q, c)))) as HPm.
  pose proof (Permutation_NoDup HPm ND) as ND2. cbn [map fst] in ND2.
  apply (proj1 (NoDup_cons_iff q _) ND2). exact (in_map fst _ _ Hin).
Qed.

Definition rbase (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (SP - 256) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.

Definition cnt_r1 : Z := cnt0 + wcalls t false + Z.of_nat (PjRoundTrip.tcalls t).
Definition cnt_r2 : Z := cnt_r1 + wcalls t true + Z.of_nat (PjRoundTrip.tcalls t).

Lemma crt_dl_perm : forall T E E', Permutation E E' -> crt_dl T E -> crt_dl T E'.
Proof.
  intros T E E' HPe (H1 & H2). split.
  - exact (Permutation_trans (Permutation_map snd (Permutation_sym HPe)) H1).
  - rewrite <- (Permutation_length HPe). exact H2.
Qed.

Lemma crt_fin_obj : forall b cnt u ms cset bf Df b4 Do Dp Dp' Do', u = JObj ms ->
  crt_dl (PjRoundTrip.ttrace u) Df ->
  crt_set_res F (rf_malloc F (crt_b2 F b cnt u Df) 37) (Z.of_nat (length ms)) (PjRoundTrip.ttrace u) b4 cset Do ->
  crt_dl (PjRoundTrip.ttrace (crt_tree u)) Dp -> Permutation Dp Dp' -> Permutation Do Do' ->
  bf = rf_frees F (rf_frees F (rf_free F (rf_run F (crt_b5 F b4 (crt_cnt2 cnt u + 1 + cset) u)
         (PjRoundTrip.ttrace (crt_tree u))) (wcap (crt_tree u) true + 16)) Dp') Do' ->
  crt_fin F b cnt u cset bf.
Proof.
  intros b cnt u ms cset bf Df b4 Do Dp Dp' Do' -> H1 H2 H3 H4 H5 E.
  unfold crt_fin. exists Df. split; [exact H1|]. cbv beta iota.
  exists b4, Do, Dp, Dp', Do'. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5 | exact E].
Qed.

Lemma crt_fin_nobj : forall b cnt u cset bf Df Db Db', tag u <> 6 ->
  crt_dl (PjRoundTrip.ttrace u) Df -> crt_dl (PjRoundTrip.ttrace u) Db -> Permutation Db Db' ->
  bf = rf_frees F (crt_b2 F b cnt u Df) Db' -> crt_fin F b cnt u cset bf.
Proof.
  intros b cnt u cset bf Df Db Db' Hty H1 H2 H3 E.
  unfold crt_fin. exists Df. split; [exact H1|].
  destruct u; try (exfalso; apply Hty; reflexivity); cbv beta iota;
    exists Db, Db'; (split; [exact H2|]); (split; [exact H3 | exact E]).
Qed.

Section Calls.
Hypothesis HRTT : forall fx, @round_trip_text_contract fx rc B API F.
Hypothesis HPS : forall fx, @pj_string_contract fx rc B API F.
Hypothesis HSET : forall fx, @pj_set_contract fx rc B API F.
Variable kw : jv -> Z.
Hypothesis HKW : forall u, (depth u <= 32)%nat -> 0 <= kw u <= PJ_PARSE_K.
Hypothesis HW : forall fx, @pj_write_hyp fx rc B API F kw.
Hypothesis HPN : forall fx, @parse_noting_contract fx rc B API F.
Hypothesis HFF : forall fx, @fuzz_free_contract fx rc B API F.
Hypothesis HPF : forall fx, @pj_free_contract fx rc B API F.
Hypothesis HSL : strlen_contract.
Hypothesis HSC : strcmp_contract.
Hypothesis HSM : same_contract.
Hypothesis HMS : memset_contract.
Hypothesis HROc : fuzz_alloc_ran_out_contract.

Lemma stpfc : forall fx L A regs mem md Lam peak cnt b tc Dc cset rv,
  gi fx L A mem md Lam peak cnt b Dc ->
  pj_node segs mem (lin Lam) (SP - 256) tc Dc -> (depth tc <= 32)%nat ->
  getr regs 1 = Z_to_bv 64 0x14250 -> getr regs 2 = Z_to_bv 64 (SP - 256) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 10 = Z_to_bv 64 (SP - 256) ->
  getr regs 26 = getr regs0 26 -> getr regs 27 = getr regs0 27 ->
  getr regs 9 = Z_to_bv 64 rv ->
  (forall Dc', Permutation Dc Dc' -> carm rv cnt (rf_frees F b Dc') cset) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 PJ_FREE) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b tc Dc cset rv HG HNc Hdc G1 G2 G3 G4 G10 G26 G27 G9 Hfin.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof alloc_ceiling_value as Hc.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _).
  assert (Hs : spZ regs = SP - 256) by (unfold spZ; rewrite G2; apply crt_uns; lia).
  assert (HK : 0 <= PJ_FREE_K (depth tc) <= CRT_K - 256) by (unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK, CRT_K; lia).
  assert (Hra : YK0s.ret_ok (getr regs 1)) by (rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (HDS : forall bk, In bk Dc -> In bk Lam)
    by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb).
  eapply SR_bind.
  { apply (HPF fx L A regs mem md Lam peak cnt (2 ^ 64 - 1) b (SP - 256) (depth tc) Dc).
    - exact (crt_renv fx L A mem md Lam peak cnt b Dc regs _ HG G2 G4 Hra HK).
    - exact HL.
    - exact Hres.
    - exact G10.
    - right. split; [lia|]. split; [exact (pj_node_fd segs _ _ _ _ _ HNc)|].
      split; [exact (crt_rplace fx L A mem md Lam peak cnt b Dc regs (SP - 256) HG Hs ltac:(lia) ltac:(lia))|].
      rewrite Hs. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  intros c' (L' & A' & regs' & mem' & md' & Lam' & -> & Hrp & Hrd & HPm & HL' & (Dc' & HPc & Hres') & _ & Hz).
  destruct (rpost_cstep B API _ L A regs mem md _ _ L' A' regs' mem' md' Hrp) as [HC2 HR].
  pose proof Hrp as (_ & _ & _ & _ & Hin' & _).
  specialize (Hz ltac:(lia)). destruct Hz as [[Hal Hstk] _].
  assert (HG' : gi fx L' A' mem' md' Lam' peak cnt (rf_frees F b Dc') []).
  { rewrite Hs in HC2.
    apply (gi_step fx fx L A mem md Lam peak cnt b Dc (SP - 256) (PJ_FREE_K (depth tc))
             (pj_free_writes (SP - 256) Dc) (freed Dc) L' A' mem' md' Lam' peak cnt (rf_frees F b Dc') []
             HG HC2).
    - unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK, CRT_K; lia.
    - lia.
    - intros a (_ & [X|[X|X]]); [left; lia | right; right; exact X | right; left; exact X].
    - intros a k Hb X. unfold freed in X. apply (HNB _ _ X). replace (a + 16 - 16) with a by lia.
      replace (k - 16 + 16) with k by lia. exact Hb.
    - intros a Ha. destruct (Z_lt_le_dec a (SP - 256 + 56)) as [X|X].
      + left. split; [lia | left; lia].
      + right. intros (_ & [Y|[Y|Y]]); [lia | | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Y; lia].
        destruct (nblk_facts L A mem md Lam peak cnt _ Dc a HM HL HDS Y) as (? & ? & _ & ? & _ & _ & ? & _). lia.
    - intros a Ha (_ & [Y|[Y|Y]]).
      + destruct Hstk as (_ & _ & Hw). destruct (Hw a ltac:(lia)) as [Hw' _]. unfold writable_at. exact Hw'.
      + destruct (nblk_facts L A mem md Lam peak cnt _ Dc a HM HL HDS Y) as (? & ? & _ & ? & _ & _ & ? & _). lia.
      + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Y. lia.
    - exact (proj1 Hrd).
    - apply Hin'. exact Hin.
    - exact Hfz.
    - exact Hfk.
    - exact HL'.
    - lia.
    - cbn [app]. apply (Permutation_app_inv_l Dc). apply (Permutation_trans (Permutation_sym HPm)). exact HP.
    - intros a k [].
    - exact Hres'. }
  rewrite G1.
  apply (st9 fx L' A' regs' mem' md' Lam' peak cnt (rf_frees F b Dc') cset rv HG').
  - rewrite <- G2. apply (HR 2). unfold callee_saved. lia.
  - rewrite <- G3. apply (HR 3). unfold callee_saved. lia.
  - rewrite <- G4. apply (HR 4). unfold callee_saved. lia.
  - rewrite <- G26. apply (HR 26). unfold callee_saved. lia.
  - rewrite <- G27. apply (HR 27). unfold callee_saved. lia.
  - rewrite <- G9. apply (HR 9). unfold callee_saved. lia.
  - exact (Hfin Dc' HPc).
Qed.

Lemma st8 : forall fx L A regs mem md Lam peak cnt b tc Dc cset rv,
  gi fx L A mem md Lam peak cnt b Dc ->
  pj_node segs mem (lin Lam) (SP - 256) tc Dc -> (depth tc <= 32)%nat -> rbase regs ->
  getr regs 9 = Z_to_bv 64 rv ->
  (forall Dc', Permutation Dc Dc' -> carm rv cnt (rf_frees F b Dc') cset) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14248) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b tc Dc cset rv HG HNo Hdo (G2 & G3 & G4 & G26 & G27) G9 Hfin.
  pose proof HG as (HC & _). pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x14250) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 2) (getr regs 11) (getr regs 12)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x15c08 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_pf1 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs' (-> & -> & ->) Hg.
  apply (stpfc fx L A regs' mem md Lam peak cnt b tc Dc cset rv HG HNo Hdo);
    try (rewrite Hg; first [reflexivity | exact G2 | exact G3 | exact G4 | exact G26 | exact G27 | exact G9]);
    assumption.
Qed.

Lemma st8z : forall fx L A regs mem md Lam peak cnt b Do cset,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt b Do ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do -> (depth (crt_tree t) <= 32)%nat -> rbase regs ->
  cnt = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) ->
  (forall Do', Permutation Do Do' -> crt_fin F b0 cnt0 t cset (rf_frees F b Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14244) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do cset (Z1 & Z2) HG HNo Hdo (G2 & G3 & G4 & G26 & G27) Hcnt Hcs Hcs0 Hfin.
  pose proof HG as (HC & _). pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x14250) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (Z_to_bv 64 0) (getr regs 2) (getr regs 11) (getr regs 12)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x15c08 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_pfz (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs' (-> & -> & ->) Hg.
  apply (stpfc fx L A regs' mem md Lam peak cnt b (crt_tree t) Do cset 0 HG HNo Hdo);
    try (rewrite Hg; first [reflexivity | exact G2 | exact G3 | exact G4 | exact G26 | exact G27]).
  intros Do' HPo. right. split; [reflexivity|]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Hcnt|].
  split; [exact Hcs|]. split; [exact Hcs0 | exact (Hfin Do' HPo)].
Qed.

Lemma stpfb : forall fx L A regs mem md Lam peak cnt b Do Dk cset,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt b (Dk ++ Do) ->
  pj_node segs mem (lin Lam) (SP - 256 + 112) (crt_tree t) Dk ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do -> (depth (crt_tree t) <= 32)%nat ->
  getr regs 1 = Z_to_bv 64 0x14244 -> getr regs 10 = Z_to_bv 64 (SP - 256 + 112) -> rbase regs ->
  cnt = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) ->
  (forall Dk' Do', Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F b Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 PJ_FREE) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do Dk cset HZ HG HNk HNo Hdo G1 G10 (G2 & G3 & G4 & G26 & G27)
    Hcnt Hcs Hcs0 Hfin.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof alloc_ceiling_value as Hc.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _).
  destruct crt_static as (_ & Herr & _).
  assert (Hs : spZ regs = SP - 256) by (unfold spZ; rewrite G2; apply crt_uns; lia).
  assert (HK : 0 <= PJ_FREE_K (depth (crt_tree t)) <= CRT_K - 256)
    by (unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK, CRT_K; lia).
  assert (Hra : YK0s.ret_ok (getr regs 1)) by (rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (HDS : forall bk, In bk Dk -> In bk Lam)
    by (intros bk Hb; apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); apply in_or_app; left; exact Hb).
  eapply SR_bind.
  { apply (HPF fx L A regs mem md Lam peak cnt (2 ^ 64 - 1) b (SP - 256 + 112) (depth (crt_tree t)) Dk).
    - exact (crt_renv fx L A mem md Lam peak cnt b (Dk ++ Do) regs _ HG G2 G4 Hra HK).
    - exact HL.
    - exact Hres.
    - exact G10.
    - right. split; [lia|]. split; [exact (pj_node_fd segs _ _ _ _ _ HNk)|].
      split; [exact (crt_rplace fx L A mem md Lam peak cnt b (Dk ++ Do) regs (SP - 256 + 112) HG Hs
                       ltac:(lia) ltac:(lia))|].
      rewrite Hs. cbn [Frame.disjoint_from]. split; [lia | exact I]. }
  intros c' (L' & A' & regs' & mem' & md' & Lam' & -> & Hrp & Hrd & HPm & HL' & (Dk' & HPk & Hres') & _ & Hz).
  destruct (rpost_cstep B API _ L A regs mem md _ _ L' A' regs' mem' md' Hrp) as [HC2 HR].
  pose proof Hrp as (_ & _ & _ & _ & Hin' & _).
  specialize (Hz ltac:(lia)). destruct Hz as [[Hal Hstk] _].
  rewrite Hs in HC2.
  assert (HPL : Permutation Lam' (Do ++ Lam0)).
  { apply (Permutation_app_inv_l Dk). apply (Permutation_trans (Permutation_sym HPm)). rewrite app_assoc. exact HP. }
  assert (HEnot : forall a, ~ (SP - 256 + 112 <= a < SP - 256 + 112 + 56) -> SP - 256 <= a < SP - 88 ->
      ~ pj_free_writes (SP - 256 + 112) Dk a).
  { intros a Ha Hw (_ & [Y|[Y|Y]]); [lia | | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Y; lia].
    destruct (nblk_facts L A mem md Lam peak cnt _ Dk a HM HL HDS Y) as (? & ? & _ & ? & _ & _ & ? & _). lia. }
  assert (HNo' : pj_node segs mem' (lin Lam') (SP - 256) (crt_tree t) Do).
  { apply (gi_node fx L A mem md Lam peak cnt b (Dk ++ Do) (SP - 256) (PJ_FREE_K (depth (crt_tree t)))
      (pj_free_writes (SP - 256 + 112) Dk) (freed Dk) L' A' mem' md' Lam' (SP - 256) (crt_tree t) Do HG HC2 HNo).
    - intros bk Hb. apply in_or_app. right. exact Hb.
    - intros bk Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. exact Hb.
    - lia.
    - lia.
    - intros a Ha. split; [unfold cwin; rewrite Herr; unfold strtod_c.STRTOD_ERRNO; lia | apply HEnot; lia].
    - intros a k Hak. split.
      + unfold freed. intros X. replace (a - 16 + 16) with a in X by lia. replace (k + 16 - 16) with k in X by lia.
        pose proof (gi_nodup _ _ _ _ _ _ _ _ _ _ HG) as ND. rewrite map_app in ND.
        exact (crt_nodup_mid _ _ a ND (in_map fst _ _ X) (in_map fst _ _ Hak)).
      + intros i Hi (_ & [Y|[Y|Y]]).
        * destruct (gi_blk_stat _ _ _ _ _ _ _ _ _ _ a k i HG (in_or_app _ _ _ (or_intror Hak)) Hi) as (_ & H1 & _). lia.
        * exact (gi_blk_sep _ _ _ _ _ _ _ _ _ _ _ a k (a + i) HG Hak ltac:(lia) Y).
        * exact (proj1 (gi_blk_stat _ _ _ _ _ _ _ _ _ _ a k i HG (in_or_app _ _ _ (or_intror Hak)) Hi) Y). }
  assert (HG' : gi fx L' A' mem' md' Lam' peak cnt (rf_frees F b Dk') Do).
  { apply (gi_step fx fx L A mem md Lam peak cnt b (Dk ++ Do) (SP - 256) (PJ_FREE_K (depth (crt_tree t)))
             (pj_free_writes (SP - 256 + 112) Dk) (freed Dk) L' A' mem' md' Lam' peak cnt (rf_frees F b Dk') Do
             HG HC2).
    - unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK, CRT_K; lia.
    - lia.
    - intros a (_ & [X|[X|X]]); [left; lia | right; right | right; left; exact X].
      destruct X as (ba & bk & Hb & Hr). exists ba, bk. split; [apply in_or_app; left; exact Hb | exact Hr].
    - intros a k Hb X. unfold freed in X. apply (HNB (a + 16) (k - 16)); [apply in_or_app; left; exact X|].
      replace (a + 16 - 16) with a by lia. replace (k - 16 + 16) with k by lia. exact Hb.
    - intros a Ha. destruct (Z_lt_le_dec a (SP - 256 + 112)) as [X|X].
      + right. apply HEnot; lia.
      + left. split; [lia | left; lia].
    - intros a Ha (_ & [Y|[Y|Y]]).
      + destruct Hstk as (_ & _ & Hw). destruct (Hw a ltac:(lia)) as [Hw' _]. unfold writable_at. exact Hw'.
      + destruct (nblk_facts L A mem md Lam peak cnt _ Dk a HM HL HDS Y) as (? & ? & _ & ? & _ & _ & ? & _). lia.
      + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Y. lia.
    - exact (proj1 Hrd).
    - apply Hin'. exact Hin.
    - exact Hfz.
    - exact Hfk.
    - exact HL'.
    - lia.
    - exact HPL.
    - intros a k Hak. apply HNB. apply in_or_app. right. exact Hak.
    - exact Hres'. }
  rewrite G1.
  apply (st8z fx L' A' regs' mem' md' Lam' peak cnt (rf_frees F b Dk') Do cset HZ HG' HNo' Hdo).
  - split; [rewrite <- G2; apply (HR 2); unfold callee_saved; lia|].
    split; [rewrite <- G3; apply (HR 3); unfold callee_saved; lia|].
    split; [rewrite <- G4; apply (HR 4); unfold callee_saved; lia|].
    split; [rewrite <- G26; apply (HR 26); unfold callee_saved; lia|].
    rewrite <- G27; apply (HR 27); unfold callee_saved; lia.
  - exact Hcnt.
  - exact Hcs.
  - exact Hcs0.
  - intros Do' HPo. exact (Hfin Dk' Do' HPk HPo).
Qed.

Lemma st7 : forall fx L A regs mem md Lam peak cnt b Do Dk cset,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt b (Dk ++ Do) ->
  pj_node segs mem (lin Lam) (SP - 256 + 112) (crt_tree t) Dk ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do -> (depth (crt_tree t) <= 32)%nat -> rbase regs ->
  cnt = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) ->
  (forall Dk' Do', Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F b Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x1423c) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do Dk cset HZ HG HNk HNo Hdo (G2 & G3 & G4 & G26 & G27) Hcnt Hcs Hcs0 Hfin.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof HG as (HC & _). pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x14244) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (Z_to_bv 64 (bv_unsigned (getr regs 2) + 112))
        (getr regs 11) (getr regs 12)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x15c08 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_ff (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs' (-> & -> & ->) Hg.
  apply (stpfb fx L A regs' mem md Lam peak cnt b Do Dk cset HZ HG HNk HNo Hdo).
  - rewrite Hg. reflexivity.
  - rewrite Hg. rewrite G2, crt_uns by lia. reflexivity.
  - split; [rewrite Hg; exact G2|]. split; [rewrite Hg; exact G3|]. split; [rewrite Hg; exact G4|].
    split; [rewrite Hg; exact G26 | rewrite Hg; exact G27].
  - exact Hcnt.
  - exact Hcs.
  - exact Hcs0.
  - exact Hfin.
Qed.

Lemma stff : forall fx L A regs mem md Lam peak cnt b Do Dk q cset,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt b (Dk ++ (q, wcap (crt_tree t) true) :: Do) ->
  pj_node segs mem (lin Lam) (SP - 256 + 112) (crt_tree t) Dk ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do -> (depth (crt_tree t) <= 32)%nat ->
  getr regs 1 = Z_to_bv 64 0x1423c -> getr regs 10 = Z_to_bv 64 q -> rbase regs ->
  cnt = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (forall ms, t = JObj ms -> In MOD_AT (map fst ms) -> cset = 0) ->
  (forall Dk' Do', Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F (rf_free F b (wcap (crt_tree t) true + 16)) Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 FUZZ_FREE) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do Dk q cset HZ HG HNk HNo Hdo G1 G10 (G2 & G3 & G4 & G26 & G27)
    Hcnt Hcs Hcs0 Hfin.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof alloc_ceiling_value as Hc.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _).
  destruct crt_static as (_ & Herr & _).
  set (cap := wcap (crt_tree t) true) in *.
  assert (Hs : spZ regs = SP - 256) by (unfold spZ; rewrite G2; apply crt_uns; lia).
  assert (Hra : YK0s.ret_ok (getr regs 1)) by (rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Hqn : In (q, cap) (Dk ++ (q, cap) :: Do)) by (apply in_or_app; right; left; reflexivity).
  pose proof (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG Hqn) as Hq.
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF (q, cap) Hq) as (Hk0 & Hqb & _). cbn [fst snd] in Hk0, Hqb.
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ q cap HM HL Hq) as (Hq1 & Hq2 & _).
  pose proof (crt_renv fx L A mem md Lam peak cnt b _ regs ALLOC_STACK HG G2 G4 Hra
    ltac:(unfold ALLOC_STACK, CRT_K; lia)) as (_ & _ & _ & _ & _ & HP1 & _).
  eapply SR_bind; [apply (HFF fx L A regs mem md q cap b Lam peak cnt (2 ^ 64 - 1) HP1 G10 HL Hro (or_intror Hq) Hres)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & Hro' & _ & Hin' & _ & Hcp & _ & Hkp & Hub & Arms).
  destruct Arms as [(Hq0 & _) | (_ & _ & (l1 & l2 & HLs & HL') & Hres')]; [lia|].
  destruct (ff_cstep B API L A regs mem md q cap L' A' regs' mem' md' HM (or_intror Hqb) Hk0 Hin' Hcp Hkp Hub)
    as [HC2 HR].
  rewrite Hs in HC2.
  assert (HPL : Permutation (l1 ++ l2) ((Dk ++ Do) ++ Lam0)).
  { rewrite HLs in HP. rewrite <- app_assoc in HP. cbn [app] in HP.
    pose proof (Permutation_app_inv _ _ _ _ _ HP) as X. rewrite app_assoc in X. exact X. }
  assert (HNE : forall a k, In (a, k) (Dk ++ Do) -> a <> q)
    by (intros a k Hak; exact (gi_fst_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG Hak)).
  assert (HIN : forall bk, In bk (Dk ++ Do) -> In bk (Dk ++ (q, cap) :: Do))
    by (intros bk Hb; destruct (in_app_or _ _ _ Hb) as [Y|Y]; apply in_or_app; [left | right; right]; exact Y).
  assert (HFW : forall a k i, In (a, k) (Dk ++ Do) -> 0 <= i < k -> ~ free_writes q cap (a + i)).
  { intros a k i Hak Hi [X|(_ & X)].
    - apply (proj1 (gi_blk_stat _ _ _ _ _ _ _ _ _ _ a k i HG (HIN _ Hak) Hi)).
      unfold alloc_statics. left. exact X.
    - exact (gi_sep2 _ _ _ _ _ _ _ _ _ _ a k q cap (a + i) HG (HIN _ Hak) Hqn (HNE a k Hak) ltac:(lia) ltac:(lia)). }
  assert (HWIN : forall a, SP - 256 <= a < SP - 88 -> ~ free_writes q cap a).
  { intros a Ha [X|(_ & X)]; [unfold G_LIVE in X; lia | lia]. }
  assert (HDK : forall bk, In bk Dk -> In bk (Dk ++ (q, cap) :: Do)) by (intros bk Hb; apply in_or_app; left; exact Hb).
  assert (HDO : forall bk, In bk Do -> In bk (Dk ++ (q, cap) :: Do))
    by (intros bk Hb; apply in_or_app; right; right; exact Hb).
  assert (HNk' : pj_node segs mem' (lin (l1 ++ l2)) (SP - 256 + 112) (crt_tree t) Dk).
  { apply (gi_node fx L A mem md Lam peak cnt b _ (SP - 256) ALLOC_STACK (free_writes q cap)
      (fun a n => a = q - 16 /\ n = cap + 16) L' A' mem' md' (l1 ++ l2) (SP - 256 + 112) (crt_tree t) Dk HG HC2 HNk HDK).
    - intros bk Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left. exact Hb.
    - lia.
    - lia.
    - intros a Ha. split; [unfold cwin; rewrite Herr; unfold strtod_c.STRTOD_ERRNO; lia | apply HWIN; lia].
    - intros a k Hak. split.
      + intros (X1 & X2). apply (HNE a k (in_or_app _ _ _ (or_introl Hak))). lia.
      + intros i Hi. exact (HFW a k i (in_or_app _ _ _ (or_introl Hak)) Hi). }
  assert (HNo2 : pj_node segs mem' (lin (l1 ++ l2)) (SP - 256) (crt_tree t) Do).
  { apply (gi_node fx L A mem md Lam peak cnt b _ (SP - 256) ALLOC_STACK (free_writes q cap)
      (fun a n => a = q - 16 /\ n = cap + 16) L' A' mem' md' (l1 ++ l2) (SP - 256) (crt_tree t) Do HG HC2 HNo HDO).
    - intros bk Hb. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right. exact Hb.
    - lia.
    - lia.
    - intros a Ha. split; [unfold cwin; rewrite Herr; unfold strtod_c.STRTOD_ERRNO; lia | apply HWIN; lia].
    - intros a k Hak. split.
      + intros (X1 & X2). apply (HNE a k (in_or_app _ _ _ (or_intror Hak))). lia.
      + intros i Hi. exact (HFW a k i (in_or_app _ _ _ (or_intror Hak)) Hi). }
  assert (HG' : gi fx L' A' mem' md' (l1 ++ l2) peak cnt (rf_free F b (cap + 16)) (Dk ++ Do)).
  { apply (gi_step fx fx L A mem md Lam peak cnt b _ (SP - 256) ALLOC_STACK
             (free_writes q cap) (fun a n => a = q - 16 /\ n = cap + 16) L' A' mem' md' (l1 ++ l2) peak cnt
             (rf_free F b (cap + 16)) (Dk ++ Do) HG HC2).
    - unfold ALLOC_STACK, CRT_K; lia.
    - lia.
    - intros a [X|(_ & X)].
      + right. left. unfold alloc_statics. left. exact X.
      + right. right. exists q, cap. split; [exact Hqn | lia].
    - intros a k Hb (X1 & X2). subst a k. exact (HNB q cap Hqn Hb).
    - intros a Ha. right. apply HWIN. lia.
    - intros a Ha X. exfalso. exact (HWIN a Ha X).
    - exact Hro'.
    - apply Hin'. exact Hin.
    - exact Hfz.
    - exact Hfk.
    - exact HL'.
    - lia.
    - exact HPL.
    - intros a k Hak. apply HNB. destruct (in_app_or _ _ _ Hak) as [Y|Y]; apply in_or_app; [left | right; right]; exact Y.
    - exact Hres'. }
  rewrite G1.
  apply (st7 fx L' A' regs' mem' md' (l1 ++ l2) peak cnt (rf_free F b (cap + 16)) Do Dk cset HZ HG' HNk' HNo2 Hdo).
  - split; [rewrite <- G2; apply (HR 2); unfold callee_saved; lia|].
    split; [rewrite <- G3; apply (HR 3); unfold callee_saved; lia|].
    split; [rewrite <- G4; apply (HR 4); unfold callee_saved; lia|].
    split; [rewrite <- G26; apply (HR 26); unfold callee_saved; lia|].
    rewrite <- G27; apply (HR 27); unfold callee_saved; lia.
  - exact Hcnt.
  - exact Hcs.
  - exact Hcs0.
  - exact Hfin.
Qed.

Lemma gi_stk_in : forall fx L A mem md Lam peak cnt b New lo hi,
  gi fx L A mem md Lam peak cnt b New -> SP - CRT_K <= lo -> lo <= hi -> hi <= SP ->
  Frame.stk segs mem lo hi.
Proof.
  intros fx L A mem md Lam peak cnt b New lo hi (HC & _) Hl Hlh Hh.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HS).
  destruct (crt_img_low B HSEG) as [_ HI]. destruct crt_sp as (Hsp1 & _ & _ & Hsp2).
  pose proof alloc_ceiling_value as Hc.
  split; [unfold CRT_K in *; lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at segs mem a) by (apply HS; left; unfold CRT_K in *; lia).
  split; [exact Hw|].
  revert Hw. unfold mrd, wa, writable_at, wview.
  destruct (mem (Z_to_bv 64 a)) as [bb|]; intros Hw; [exists bb; reflexivity|].
  rewrite MState.unsigned_lit in Hw by (unfold CRT_K in *; lia).
  destruct (find_segment segs a 1) as [seg|] eqn:Fs; [|contradiction].
  exfalso. destruct (HI a seg Fs). unfold CRT_K in *. lia.
Qed.

Lemma gi_stk : forall fx L A mem md Lam peak cnt b New,
  gi fx L A mem md Lam peak cnt b New -> Frame.stk segs mem (SP - CRT_K) (SP - 256).
Proof.
  intros fx L A mem md Lam peak cnt b New HG.
  apply (gi_stk_in _ _ _ _ _ _ _ _ _ _ _ _ HG); unfold CRT_K; lia.
Qed.

Definition crt_m (u : jv) : Z := crt_count u 3.

Lemma crt_count_le : forall tt cset, 0 <= cset <= 3 -> 0 <= crt_count tt cset <= crt_m tt.
Proof. intros tt cset Hc. unfold crt_m, crt_count, wcalls. destruct tt; cbv beta iota; lia. Qed.

Lemma crt_m_split : forall u, crt_m u <= wcalls u false + wcalls u true + 2 * Z.of_nat (PjRoundTrip.tcalls u) + 4 +
  wcalls (crt_tree u) true + Z.of_nat (PjRoundTrip.tcalls (crt_tree u)).
Proof. intros u. unfold crt_m, crt_count, wcalls. destruct u; cbv beta iota; lia. Qed.

Lemma crt_m_le : 0 <= crt_m t <= 2 ^ 29.
Proof.
  assert (Hu0 : PjRoundTrip.pj_wf jr_strtod t) by (eapply PjRoundTrip.wf_read; exact HX).
  pose proof (crt_wf x t HX) as Hu1.
  assert (T0 : (PjRoundTrip.tcalls t <= 2 * length (wdoc t false) + 2)%nat).
  { rewrite <- (PjRoundTrip.G9_calls _ _ Hu0 false). unfold ncalls. apply G7_4. }
  assert (T1 : (PjRoundTrip.tcalls (crt_tree t) <= 2 * length (wdoc (crt_tree t) true) + 2)%nat).
  { rewrite <- (PjRoundTrip.G9_calls _ _ Hu1 true). unfold ncalls. apply G7_4. }
  pose proof (crt_len t) as E1.
  pose proof (crt_rf_wcalls t false) as W0. pose proof (crt_rf_wcalls t true) as W1.
  pose proof (crt_rf_wcalls (crt_tree t) true) as W2.
  pose proof (crt_m_split t) as S. pose proof (crt_count_le t 3 ltac:(lia)) as P.
  unfold wlen in *. lia.
Qed.

Lemma crt_blk_nown : forall L A mem md a k y, MR L A mem md -> In (a, k) (blocks L A) -> a <= y < a + k ->
  ~ owned B L A y.
Proof.
  intros L A mem md a k y HM Hin Hy. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & E1 & Hp).
  cbn [fst snd] in E1. injection E1 as E1 E2. subst n.
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p k (y - a) HM Hp ltac:(lia)) as (_ & _ & _ & H).
  rewrite E1 in H. replace (a + (y - a)) with y in H by lia. exact H.
Qed.

Lemma crt_errno_img : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof.
  intros a Ha. destruct crt_static as (_ & Herr & _). rewrite Herr in Ha.
  unfold in_img. rewrite HSEG.
  split; [intros E; apply (f_equal (@length Segment)) in E; vm_compute in E; discriminate E|].
  assert (C1 : existsb (fun r => (bv_unsigned (fst r) <=? strtod_c.STRTOD_ERRNO) &&
                 (strtod_c.STRTOD_ERRNO + 4 <=? bv_unsigned (fst r) + bv_unsigned (snd r))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C1 as (r1 & H1 & E1). apply andb_prop in E1 as [E1 F1]. apply Z.leb_le in E1, F1.
  exists r1. split; [assumption | lia].
Qed.

Lemma crt_lam_text : forall fx L A mem md Lam peak cnt b New regs q k len,
  gi fx L A mem md Lam peak cnt b New -> In (q, k) Lam -> 0 <= len <= k ->
  text_ok B L A Lam regs q len.
Proof.
  intros fx L A mem md Lam peak cnt b New regs q k len HG Hq Hlen.
  pose proof HG as (HC & _ & _ & _ & _ & HL & _). pose proof HC as (HM & _).
  pose proof HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF (q, k) Hq) as (Hk0 & Hqb & _ & Himg). cbn [fst snd] in Hk0, Hqb, Himg.
  split; [right; right; right; exists q, k; unfold lin; split; [exact Hq | lia]|].
  intros i Hi.
  assert (Hni : ~ in_img B (q + i)) by (replace (q + i) with (q - 16 + (i + 16)) by lia; apply Himg; lia).
  split; [exact (crt_blk_nown L A mem md (q - 16) (k + 16) (q + i) HM Hqb ltac:(lia))|].
  split; [intros Hs; exact (Hni (crt_statics_img _ Hs)) | intros He; exact (Hni (crt_errno_img _ He))].
Qed.

Lemma crt_node_wr : forall m lb p u Du, pj_node segs m lb p u Du -> forall a, p <= a < p + 56 -> writable_at segs m a.
Proof.
  intros m lb p u Du H a Ha.
  destruct u; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & _ & Hw) & _) & _); exact (proj1 (Hw a Ha)).
Qed.

Lemma crt_zb : forall w, Forall (fun c => 0 < c < 256) w -> zb (map (Z_to_bv 8) w) = w.
Proof.
  intros w H. unfold zb. rewrite map_map. transitivity (map (fun c => c) w); [|apply map_id].
  apply map_ext_in. intros c Hc. rewrite Forall_forall in H. pose proof (H c Hc) as Hr.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.


Lemma crt_tdep : (depth t <= 32)%nat /\ (depth (crt_tree t) <= 32)%nat.
Proof.
  assert (H : (depth t <= MAXD)%nat) by (eapply json_read_depth; exact HX).
  pose proof (crt_depth t) as H2. unfold MAXD in H. split; lia.
Qed.

Lemma crt_ro_hi : forall a : word, alloc_ceiling <= bv_unsigned a -> ro_addr rsegs a = false.
Proof.
  intros a Ha. destruct (crt_img_low B HSEG) as [_ HI]. unfold ro_addr. rewrite <- HSEG.
  destruct (find_segment (ms_segs B) (bv_unsigned a) 1) as [g|] eqn:Fs; [destruct (HI _ g Fs); lia | reflexivity].
Qed.

Lemma crt_stk_norm : forall m lo hi, stk rsegs m lo hi -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hl Hh. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & bb & Hb).
  assert (Hr : ro_addr rsegs (wa a) = false) by (apply crt_ro_hi; rewrite unsigned_lit by lia; lia).
  unfold wview, mrd, normalize in *. cbv beta. rewrite Hr. split; [exact Hw | exists bb; exact Hb].
Qed.

Lemma crt_node_norm : forall L A mem Lam peak cnt fail p tc Dc,
  ledger B L A mem Lam peak cnt fail -> (forall bk, In bk Dc -> In bk Lam) -> ro_agree rsegs mem ->
  pj_node segs mem (lin Lam) p tc Dc -> alloc_ceiling <= p -> p + 56 <= 2 ^ 64 ->
  pj_node rsegs (normalize rsegs mem) (lin Lam) p tc Dc.
Proof.
  intros L A mem Lam peak cnt fail p tc Dc HL HD Hro HN Hp1 Hp2.
  unfold segs in HN. rewrite HSEG in HN.
  apply (pj_node_frame rsegs tc mem (lin Lam) (normalize rsegs mem) (lin Lam) p Dc HN (fun a k H => HD _ H)).
  intros w Hx. pose proof (bv_unsigned_in_range 64 w) as Rx. unfold bv_modulus in Rx. cbn in Rx.
  rewrite <- (wa_of_var w (bv_unsigned w) eq_refl). unfold wa.
  remember (bv_unsigned w) as a eqn:Ea. clear Ea.
  apply (crt_raw rsegs); [symmetry; exact (mbyte_rel rsegs mem (normalize rsegs mem) a (mem_rel_normalize rsegs mem Hro))|].
  rewrite <- HSEG.
  destruct Hx as [Hx|([ba bk] & Hb & Hx)].
  - apply (crt_noseg_hi B (crt_img_low B HSEG)). lia.
  - unfold pj_holds in Hx. cbn [fst snd] in Hx.
    destruct HL as (_ & _ & _ & _ & _ & HF'). rewrite Forall_forall in HF'.
    destruct (HF' (ba, bk) (HD _ Hb)) as (Hk0 & Hin & _ & Himg). cbn [fst snd] in Hk0, Hin, Himg.
    apply (crt_noseg B HSEG a ltac:(lia)). replace a with (ba - 16 + (a - ba + 16)) by lia. apply Himg. lia.
Qed.

Lemma crt_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_kAn : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree rsegs mem1 ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize rsegs mem1)
    (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' m0 regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom rsegs)) ->
     mem_rel rsegs mem' m0 -> ro_same rsegs mem1 mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR segs (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom segs)) md1) P) ->
  SR segs (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom segs)) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz Hro HE HS HK.
  apply (kb_run (fx := fx1) B regs1 pc mem1 md1
    (fun R pc' mem' => exists s0, Q s0 /\ ms_rel rsegs (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem'
       (seg_rom rsegs)) s0 /\ ro_same rsegs mem1 mem') P Hh Hz).
  - unfold segs. rewrite HSEG.
    eapply Exec.evt_mono; [eapply (evt_normalize rsegs); [exact crt_wx | exact Hro | exact HE]|].
    intros ms' (s0 & HQ & Hrel & Hsame). destruct (HS s0 HQ) as (R & pc0 & m0 & ->).
    destruct ms' as [R' F' pc'' svc' rv' fc' m' ro'].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS] in *. subst.
    exists R, pc0, m'. split; [reflexivity|]. exists (MState.MS R fp_regs pc0 fp_csr None m0 (seg_rom rsegs)).
    split; [exact HQ|]. split; [|exact Hsame].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HR].
  - intros R pc' mem' regs' (s0 & HQ & Hrel & Hsame) HGr.
    destruct (HS s0 HQ) as (R0 & pc0 & m0 & E0). subst s0.
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS] in *.
    subst R0 pc0.
    exact (HK R pc' mem' m0 regs' HQ HR Hsame HGr).
Qed.

Ltac crt_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM;
  subst R pc m; clear E.

Lemma gi_D : forall fx L A mem md Lam peak cnt b New,
  gi fx L A mem md Lam peak cnt b New -> forall bk, In bk D -> In bk Lam.
Proof.
  intros fx L A mem md Lam peak cnt b New (_ & _ & _ & _ & _ & _ & _ & HP & _) bk Hb.
  apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact (HD0 _ Hb).
Qed.

Lemma gi_foot : forall fx L A mem md Lam peak cnt b New p Dc z,
  gi fx L A mem md Lam peak cnt b New -> (forall bk, In bk Dc -> In bk Lam) ->
  pj_foot p Dc z -> (p <= z < p + 56) \/ (4096 <= z < alloc_ceiling).
Proof.
  intros fx L A mem md Lam peak cnt b New p Dc z HG HD [Hx|([ba bk] & Hb & Hx)]; [left; exact Hx|].
  pose proof HG as (HC & _ & _ & _ & _ & HL & _). pose proof HC as (HM & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ ba bk HM HL (HD _ Hb)) as (H1 & H2 & _).
  unfold pj_holds in Hx. cbn [fst snd] in Hx. right. lia.
Qed.

Lemma gi_munch : forall fx L A mem md Lam peak cnt b New mem2 W,
  gi fx L A mem md Lam peak cnt b New ->
  Frame.munch W mem mem2 -> Frame.wmono segs mem mem2 -> ro_agree segs mem2 ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (SP - CRT_K <= z < SP - 256) -> Frame.outside W z) ->
  gi fx L A mem2 md Lam peak cnt b New.
Proof.
  intros fx L A mem md Lam peak cnt b New mem2 W
    (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN) Hm Hw Hro2 HO.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof HC as (HM & _).
  assert (HC2 : cstep B API SP CRT_K alloc_statics NoG L0 A0 mem0 md0 L A mem2 md).
  { apply (cstep_munch B API SP CRT_K alloc_statics NoG L0 A0 mem0 md0 L A mem md mem2 W (crt_img_low B HSEG));
      [unfold CRT_K; lia | exact HC | exact Hm | exact Hw |].
    intros z Hz Hn. apply HO; [exact Hz | lia]. }
  refine (conj HC2 (conj Hro2 (conj Hin (conj Hfz (conj Hfk (conj _ (conj Hpk (conj HP (conj HNB (conj Hres
    (conj _ _))))))))))).
  - apply (ledger_munch B API L A mem md mem2 Lam peak cnt _ W HM HL Hm).
    intros z Hz. apply HO; [lia | unfold CRT_K; lia].
  - apply (crt_rw_frame segs mem mem2 (SP - 88) cells0 Hcells).
    intros i Hi. assert (Hcs : Z.of_nat (cells_size cells0) = 88) by reflexivity. rewrite Hcs in Hi.
    assert (Ho : Frame.outside W (SP - 88 + i)) by (apply HO; lia).
    split; [exact (mbyte_munch segs W mem mem2 (SP - 88 + i) Hm ltac:(lia) Ho)|].
    exact (proj1 (writable_munch segs W mem mem2 (SP - 88 + i) Hm ltac:(lia) Ho)).
  - apply (pj_node_munch segs W mem (lin Lam) mem2 (lin Lam) doc t D HN
      (fun a k H => gi_D _ _ _ _ _ _ _ _ _ _
        (conj HC (conj Hro (conj Hin (conj Hfz (conj Hfk (conj HL (conj Hpk (conj HP (conj HNB (conj Hres
          (conj Hcells HN))))))))))) _ H) Hm).
    intros z Hz. destruct Hz as [Hz|([ba bk] & Hb & Hz)].
    + apply HO; lia.
    + destruct (ledger_block_range B API L A mem md Lam peak cnt _ ba bk HM HL
        (gi_D _ _ _ _ _ _ _ _ _ _
          (conj HC (conj Hro (conj Hin (conj Hfz (conj Hfk (conj HL (conj Hpk (conj HP (conj HNB (conj Hres
            (conj Hcells HN))))))))))) _ Hb)) as (H1 & H2 & _).
      unfold pj_holds in Hz. cbn [fst snd] in Hz. apply HO; [lia | unfold CRT_K; lia].
Qed.

Lemma st6 : forall fx L A regs mem md Lam peak cnt b Do Dk q ms cset,
  ro = 0 /\ oo = 0 ->
  t = JObj ms ->
  gi fx L A mem md Lam peak cnt b (Dk ++ (q, wcap (crt_tree t) true) :: Do) ->
  pj_node segs mem (lin Lam) (SP - 256 + 112) (crt_tree t) Dk ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 doc -> getr regs 9 = Z_to_bv 64 q ->
  getr regs 18 = Z_to_bv 64 CRT_S2 ->
  getr regs 19 = Z_to_bv 64 (Z.of_nat (length ms)) -> rbase regs ->
  cnt = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (In MOD_AT (map fst ms) -> cset = 0) ->
  (forall Dk' Do', Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F (rf_free F b (wcap (crt_tree t) true + 16)) Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x140fc) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do Dk q ms cset HZ Ht HG HNk HNo G10 G8 G9 G18 G19
    (G2 & G3 & G4 & G26 & G27) Hcnt Hcs Hcs0 Hfin.
  destruct crt_sp as (Hsp1 & _ & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof crt_tdep as (_ & Hdo).
  pose proof (gi_flags _ _ _ _ _ _ _ _ _ _ HG) as (HF1 & HF2).
  destruct HZ as (Z1 & Z2). rewrite Z1 in HF1. rewrite Z2 in HF2.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  set (cap := wcap (crt_tree t) true) in *.
  set (ms' := pj_set_model ms MOD_AT (JStr STAMP)).
  assert (Etr : crt_tree t = JObj ms') by (rewrite Ht; reflexivity).
  assert (Hs : bv_unsigned (getr regs 2) = SP - 256) by (rewrite G2; apply crt_uns; lia).
  assert (Hpos : 0 <= SP - 256) by lia.
  assert (HDk : forall bk, In bk Dk -> In bk Lam)
    by (intros bk Hb; apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); apply in_or_app; left; exact Hb).
  assert (HDo : forall bk, In bk Do -> In bk Lam)
    by (intros bk Hb; apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); apply in_or_app; right; right; exact Hb).
  assert (HDd : forall bk, In bk D -> In bk Lam) by exact (gi_D _ _ _ _ _ _ _ _ _ _ HG).
  pose proof (gi_stk _ _ _ _ _ _ _ _ _ _ HG) as Hstk.
  unfold segs in Hro, Hstk, HF1, HF2. rewrite HSEG in Hro, Hstk, HF1, HF2.
  eapply (crt_kAn fx regs _ mem md _ cpost Hh Hz Hro).
  { unfold rmk. rewrite G10, G18.
    eapply evt_cut.
    { apply (crt_pn HROc (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
        (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem)).
      - exact (bytes_at_normalize rsegs mem _ _ Hro HF2).
      - exact (bytes_at_normalize rsegs mem _ _ Hro HF1). }
    intros ms1 E1. cbv beta in E1. subst ms1.
    apply (crt_cmp HSC HSM (Z_to_bv 64 0x1410c) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (Z_to_bv 64 0) (getr regs 11) (getr regs 12) (getr regs 13)
      (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (Z_to_bv 64 CRT_S2) (getr regs 19) (Z_to_bv 64 0)
      (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem) (SP - CRT_K) doc
      (lin Lam) ms ms' D Dk (crt_at ms) G8 G19 eq_refl).
    - pose proof (crt_node_norm L A mem Lam peak cnt _ doc t D HL HDd Hro HN ltac:(lia) ltac:(lia)) as X.
      rewrite Ht in X. exact X.
    - rewrite Hs. pose proof (crt_node_norm L A mem Lam peak cnt _ (SP - 256 + 112) (crt_tree t) Dk HL HDk Hro HNk
        ltac:(lia) ltac:(lia)) as X. rewrite Etr in X. exact X.
    - exact (crt_set_rel_model ms).
    - exact (crt_modat_img _ (mem_inv_normalize rsegs mem)).
    - exact (crt_stamp_img _ (mem_inv_normalize rsegs mem)).
    - exact (mem_inv_normalize rsegs mem).
    - rewrite Hs. apply crt_stk_norm; [exact Hstk | unfold CRT_K; lia | lia].
    - rewrite Hs. unfold same_k, SAME_FS. pose proof crt_tdep as (Hdt & _). rewrite Ht in Hdt. unfold CRT_K. lia.
    - intros z Hzf. rewrite Hs. cbn [Frame.outside].
      destruct (gi_foot _ _ _ _ _ _ _ _ _ _ doc D z HG HDd Hzf); unfold CRT_K; (split; [lia | exact I]).
    - intros z Hzf. rewrite Hs in Hzf |- *. cbn [Frame.outside].
      destruct (gi_foot _ _ _ _ _ _ _ _ _ _ _ Dk z HG HDk Hzf); unfold CRT_K; (split; [lia | exact I]). }
  { intros ms0 (t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' &
      s8' & s9' & t3' & t4' & t5' & t6' & m' & E & _). eexists _, _, _. exact E. }
  intros R pc' mem' m0 regs' HQ HR Hsame HGr.
  destruct HQ as (t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' &
    s8' & s9' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & _).
  crt_inj E R pc' m0.
  rewrite Hs in MU.
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (munch_rel rsegs _ mem _ mem' m' HR0 HR Hsame MU) as MU'.
  pose proof (wmono_rel rsegs mem _ mem' m' HR0 HR Hsame WM) as WM'.
  pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as Hro'.
  unfold segs in HG, HNk, HNo. rewrite <- HSEG in WM', Hro'.
  assert (HO : forall z, 0 <= z < 2 ^ 64 -> ~ (SP - CRT_K <= z < SP - 256) ->
      Frame.outside [(SP - CRT_K, SP - 256)] z) by (intros z Hzf Hn; cbn [Frame.outside]; split; [lia | exact I]).
  pose proof (gi_munch _ _ _ _ _ _ _ _ _ _ _ _ HG MU' WM' Hro' HO) as HG'.
  change (Z_to_bv 64 0x157f8) with (Z_to_bv 64 FUZZ_FREE).
  apply (stff fx L A regs' mem' md Lam peak cnt b Do Dk q cset (conj Z1 Z2) HG').
  - apply (pj_node_munch segs _ mem (lin Lam) mem' (lin Lam) _ _ _ HNk (fun a k H => HDk _ H) MU').
    intros z Hzf. destruct (gi_foot _ _ _ _ _ _ _ _ _ _ _ Dk z HG HDk Hzf); cbn [Frame.outside];
      unfold CRT_K; (split; [lia | exact I]).
  - apply (pj_node_munch segs _ mem (lin Lam) mem' (lin Lam) _ _ _ HNo (fun a k H => HDo _ H) MU').
    intros z Hzf. destruct (gi_foot _ _ _ _ _ _ _ _ _ _ _ Do z HG HDo Hzf); cbn [Frame.outside];
      unfold CRT_K; (split; [lia | exact I]).
  - exact Hdo.
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G9.
  - split; [rewrite HGr; exact G2|]. split; [rewrite HGr; exact G3|]. split; [rewrite HGr; exact G4|].
    split; [rewrite HGr; exact G26 | rewrite HGr; exact G27].
  - exact Hcnt.
  - exact Hcs.
  - intros ms1 E1 Hin1. rewrite Ht in E1. injection E1 as <-. exact (Hcs0 Hin1).
  - exact Hfin.
Qed.

Lemma stpp : forall fx L A regs mem md Lam peak cnt b Do q ms cset,
  ro = 0 /\ oo = 0 ->
  t = JObj ms ->
  gi fx L A mem md Lam peak cnt b ((q, wcap (crt_tree t) true) :: Do) ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do ->
  Mem.bytes_at segs mem q (map (Z_to_bv 8) (wdoc (crt_tree t) true ++ [0])) ->
  Forall (fun c => 0 < c < 256) (wdoc (crt_tree t) true) ->
  getr regs 1 = Z_to_bv 64 0x140fc -> getr regs 10 = Z_to_bv 64 q ->
  getr regs 11 = Z_to_bv 64 (wlen (crt_tree t) true) -> getr regs 12 = Z_to_bv 64 (SP - 256 + 112) ->
  getr regs 8 = Z_to_bv 64 doc -> getr regs 9 = Z_to_bv 64 q -> getr regs 18 = Z_to_bv 64 CRT_S2 ->
  getr regs 19 = Z_to_bv 64 (Z.of_nat (length ms)) -> rbase regs ->
  cnt + Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (In MOD_AT (map fst ms) -> cset = 0) ->
  room_run F b (PjRoundTrip.ttrace (crt_tree t)) ->
  (forall Dk Dk' Do', crt_dl (PjRoundTrip.ttrace (crt_tree t)) Dk -> Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F (rf_free F (rf_run F b (PjRoundTrip.ttrace (crt_tree t)))
       (wcap (crt_tree t) true + 16)) Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 PARSE_NOTING) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do q ms cset HZ Ht HG HNo HB HFw G1 G10 G11 G12 G8 G9 G18 G19
    (G2 & G3 & G4 & G26 & G27) Hcnt Hcs Hcs0 HRR Hfin.
  pose proof (proj1 (gi_flags _ _ _ _ _ _ _ _ _ _ HG)) as HF1. rewrite (proj1 HZ) in HF1.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  destruct crt_static as (_ & Herr & _).
  pose proof (crt_count_le t cset Hcs) as Hcl0. pose proof crt_m_le as Hm0.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  pose proof HL as (_ & _ & Hcn & _).
  pose proof (crt_wf x t HX) as Hu.
  assert (Hwl : wlen (crt_tree t) true + 1 <= 2 ^ 28).
  { unfold wlen in *. pose proof (crt_len t) as H1. lia. }
  pose proof (RttModel.wcap_ge (crt_tree t) true ltac:(lia)) as Hcap.
  assert (Hqn : In (q, wcap (crt_tree t) true) ((q, wcap (crt_tree t) true) :: Do)) by (left; reflexivity).
  pose proof (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG Hqn) as Hq.
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ _ _ HM HL Hq) as (Hq1 & Hq2 & _).
  rewrite map_app in HB. apply (proj1 (bytes_at_app segs mem q _ _)) in HB. destruct HB as [HB _].
  pose proof (crt_zb _ HFw) as Hzb.
  assert (Hs : spZ regs = SP - 256) by (unfold spZ; rewrite G2; apply crt_uns; lia).
  assert (HK : 0 <= PN_K <= CRT_K - 256) by (unfold CRT_K; split; apply Z.leb_le; vm_compute; reflexivity).
  assert (Hra : YK0s.ret_ok (getr regs 1)) by (rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Htc : Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) <= crt_count t cset)
    by (unfold crt_count; rewrite Ht; cbv beta iota; unfold wcalls; lia).
  eapply SR_bind.
  { apply (HPN fx L A regs mem md Lam peak cnt (2 ^ 64 - 1) b q (wlen (crt_tree t) true) (SP - 256 + 112)
      (map (Z_to_bv 8) (wdoc (crt_tree t) true))).
    - exact (crt_renv fx L A mem md Lam peak cnt b _ regs _ HG G2 G4 Hra HK).
    - exact HL.
    - exact Hres.
    - exact G10.
    - exact G11.
    - exact G12.
    - lia.
    - lia.
    - lia.
    - unfold wlen. rewrite length_map. reflexivity.
    - exact HB.
    - rewrite Hzb. pose proof (PjRoundTrip.G12_1 (wdoc (crt_tree t) true)) as H. unfold wlen in Hwl. lia.
    - exact (crt_lam_text fx L A mem md Lam peak cnt b _ regs q (wcap (crt_tree t) true) (wlen (crt_tree t) true)
        HG Hq ltac:(unfold wlen in *; lia)).
    - lia.
    - split; [Z.div_mod_to_equations; lia|].
      apply (gi_stk_in _ _ _ _ _ _ _ _ _ _ _ _ HG); unfold CRT_K; lia.
    - exact (crt_rplace fx L A mem md Lam peak cnt b _ regs (SP - 256 + 112) HG Hs ltac:(lia) ltac:(lia)).
    - intros a k Hak. right. destruct (ledger_block_range B API L A mem md Lam peak cnt _ _ _ HM HL Hak). lia.
    - cbn [Frame.disjoint_from]. split; [lia | exact I].
    - exact HF1.
    - cbn [Frame.disjoint_from].
      assert (Gimg : in_img B G_RAN_OUT) by (destruct (HGF G_RAN_OUT crt_gro_in) as (X & _); exact X).
      pose proof HL as (_ & _ & _ & _ & _ & HFq). rewrite Forall_forall in HFq.
      destruct (HFq (q, wcap (crt_tree t) true) Hq) as (_ & _ & _ & Himq). cbn [fst snd] in Himq.
      assert (Hgl : G_RAN_OUT < alloc_ceiling) by (unfold G_RAN_OUT; lia).
      split; [|split; [lia | exact I]].
      destruct (Z_lt_le_dec G_RAN_OUT q) as [X|X]; [left; lia|].
      destruct (Z_lt_le_dec G_RAN_OUT (q + wlen (crt_tree t) true)) as [Y|Y]; [|right; lia].
      exfalso. apply (Himq (G_RAN_OUT - (q - 16))); [unfold wlen in *; lia|].
      replace (q - 16 + (G_RAN_OUT - (q - 16))) with G_RAN_OUT by lia. exact Gimg.
    - rewrite Hs. cbn [Frame.disjoint_from]. unfold CRT_K in HK. split; [lia|]. split; [lia | exact I].
    - lia.
    - rewrite Hzb, (PjRoundTrip.G9_trace _ _ Hu true). exact HRR. }
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & ok & res & tr & -> & FZ2 & FK2 &
    RP2 & RD2 & _ & LG2 & Hrun & Hoks & Hcnt2 & Hfa & Hpk2 & Hhp & Hst & Hfull & Hres2).
  assert (Hcalls : ncalls jr_strtod (zb (map (Z_to_bv 8) (wdoc (crt_tree t) true))) =
      PjRoundTrip.tcalls (crt_tree t)) by (rewrite Hzb; exact (PjRoundTrip.G9_calls _ _ Hu true)).
  assert (Hfp : 2 ^ 64 - 1 < cnt \/
      cnt + Z.of_nat (ncalls jr_strtod (zb (map (Z_to_bv 8) (wdoc (crt_tree t) true)))) <= 2 ^ 64 - 1)
    by (right; rewrite Hcalls; lia).
  destruct (Hfull Hfp) as [Eres Hcl].
  rewrite Hzb, (PjRoundTrip.G9 _ _ Hu true) in Eres. subst res.
  rewrite Hcalls in Hcl.
  destruct (crt_rf_trace _ _ _ _ _ _ Hrun Hoks ltac:(rewrite Hcl; lia)) as [_ Etr].
  rewrite Hzb, (PjRoundTrip.G9_trace _ _ Hu true) in Etr. subst tr.
  destruct Hres2 as (G10' & Hres' & D' & HPm & HLz & HNl & HNB' & HND).
  assert (Hf2 : fail2 = 2 ^ 64 - 1) by (apply (proj2 Hfa); rewrite Hcl; lia).
  rewrite Hf2 in LG2.
  destruct (rpost_cstep B API _ L A regs mem md _ _ L2 A2 regs2 mem2 md2 RP2) as [HC2 HR].
  pose proof RP2 as (_ & _ & _ & _ & Hin' & _).
  rewrite Hs in HC2.
  assert (HDo2 : forall bk, In bk Do -> In bk Lam2).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right.
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. right. exact Hb. }
  assert (HG' : gi fx2 L2 A2 mem2 md2 Lam2 peak2 cnt2 (rf_run F b (PjRoundTrip.ttrace (crt_tree t)))
      (D' ++ (q, wcap (crt_tree t) true) :: Do)).
  { apply (gi_step fx fx2 L A mem md Lam peak cnt b _ (SP - 256) PN_K (parse_noting_writes (SP - 256 + 112))
             (fun _ _ => False) L2 A2 mem2 md2 Lam2 peak2 cnt2 (rf_run F b (PjRoundTrip.ttrace (crt_tree t))) _
             HG HC2).
    - unfold CRT_K in *. lia.
    - lia.
    - intros a [X|X]; [left; lia | right; left; exact X].
    - intros a k _ Hf. exact Hf.
    - intros a Ha. unfold parse_noting_writes, pj_parse_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    - intros a Ha [X|X]; [exact (crt_node_wr _ _ _ _ _ HND a X)|].
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
    - exact (proj1 RD2).
    - apply Hin'. exact Hin.
    - exact FZ2.
    - intros r Hr. rewrite (FK2 r Hr). exact (Hfk r Hr).
    - exact LG2.
    - rewrite Hpk2. lia.
    - rewrite <- app_assoc. exact (Permutation_trans HPm (Permutation_app_head D' HP)).
    - intros a k Hak. destruct (in_app_or _ _ _ Hak) as [Y|Y].
      + intros Hb. apply (HNB' a k Y). exact (HPers _ _ Hb (fun z => z)).
      + exact (HNB a k Y).
    - exact Hres'. }
  rewrite G1.
  apply (st6 fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 (rf_run F b (PjRoundTrip.ttrace (crt_tree t))) Do D' q ms cset
    HZ Ht HG' HND).
  - apply (gi_node fx L A mem md Lam peak cnt b _ (SP - 256) PN_K (parse_noting_writes (SP - 256 + 112))
      (fun _ _ => False) L2 A2 mem2 md2 Lam2 (SP - 256) (crt_tree t) Do HG HC2 HNo).
    + intros bk Hb. right. exact Hb.
    + exact HDo2.
    + lia.
    + lia.
    + intros a Ha. split; [unfold cwin; rewrite Herr; unfold strtod_c.STRTOD_ERRNO; unfold CRT_K in HK; lia|].
      intros [X|X]; [lia | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X; lia].
    + intros a k Hak. split; [intros Hf; exact Hf|]. intros i Hi [X|X].
      * destruct (gi_blk_stat _ _ _ _ _ _ _ _ _ _ a k i HG (or_intror Hak) Hi) as (_ & H1 & _). lia.
      * exact (proj1 (gi_blk_stat _ _ _ _ _ _ _ _ _ _ a k i HG (or_intror Hak) Hi) X).
  - exact G10'.
  - rewrite <- G8. apply (HR 8). unfold callee_saved. lia.
  - rewrite <- G9. apply (HR 9). unfold callee_saved. lia.
  - rewrite <- G18. apply (HR 18). unfold callee_saved. lia.
  - rewrite <- G19. apply (HR 19). unfold callee_saved. lia.
  - split; [rewrite <- G2; apply (HR 2); unfold callee_saved; lia|].
    split; [rewrite <- G3; apply (HR 3); unfold callee_saved; lia|].
    split; [rewrite <- G4; apply (HR 4); unfold callee_saved; lia|].
    split; [rewrite <- G26; apply (HR 26); unfold callee_saved; lia|].
    rewrite <- G27; apply (HR 27); unfold callee_saved; lia.
  - rewrite Hcnt2, Hcl. lia.
  - exact Hcs.
  - exact Hcs0.
  - intros Dk' Do' H1 H2. exact (Hfin D' Dk' Do' (conj HLz HNl) H1 H2).
Qed.

Lemma crt_blk_align : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) -> a mod 16 = 0.
Proof.
  intros L A mem md a k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & E1 & Hp).
  cbn [fst snd] in E1. injection E1 as E1 E2. subst n. rewrite <- E1.
  exact (mr_blocks_aligned _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Lemma crt_bytes_of_present : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (a + i)) ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a H0 H1 HP.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (HP 0 ltac:(lia)) as (bb & Hb). rewrite Z.add_0_r in Hb.
    assert (HP' : forall i, 0 <= i < Z.of_nat n -> present m (a + 1 + i))
      by (intros i Hi; replace (a + 1 + i) with (a + (i + 1)) by lia; apply HP; lia).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) HP') as (bs & Hl & HB).
    exists (bb :: bs). split; [cbn; lia|].
    change (bb :: bs) with ([bb] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [bb] bs)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
      assert (i = 0%nat) by lia. subst i. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
      cbn [nth_error]. unfold mrd, wa. rewrite Hb. reflexivity.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HB.
Qed.

Lemma st5 : forall fx L A regs mem md Lam peak cnt b Do q ms cset,
  ro = 0 /\ oo = 0 ->
  t = JObj ms ->
  gi fx L A mem md Lam peak cnt b ((q, wcap (crt_tree t) true) :: Do) ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do ->
  Mem.bytes_at segs mem q (map (Z_to_bv 8) (wdoc (crt_tree t) true ++ [0])) ->
  Forall (fun c => 0 < c < 256) (wdoc (crt_tree t) true) ->
  getr regs 10 = Z_to_bv 64 q -> getr regs 8 = Z_to_bv 64 doc ->
  getr regs 18 = Z_to_bv 64 CRT_S2 ->
  getr regs 19 = Z_to_bv 64 (Z.of_nat (length ms)) -> rbase regs ->
  cnt + Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) = cnt0 + crt_count t cset -> 0 <= cset <= 3 ->
  (In MOD_AT (map fst ms) -> cset = 0) ->
  room_run F b (PjRoundTrip.ttrace (crt_tree t)) ->
  (forall Dk Dk' Do', crt_dl (PjRoundTrip.ttrace (crt_tree t)) Dk -> Permutation Dk Dk' -> Permutation Do Do' ->
     crt_fin F b0 cnt0 t cset (rf_frees F (rf_frees F (rf_free F (rf_run F b (PjRoundTrip.ttrace (crt_tree t)))
       (wcap (crt_tree t) true + 16)) Dk') Do')) ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x140cc) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do q ms cset HZ Ht HG HNo HB HFw G10 G8 G18 G19
    (G2 & G3 & G4 & G26 & G27) Hcnt Hcs Hcs0 HRR Hfin.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof (gi_flags _ _ _ _ _ _ _ _ _ _ HG) as (HF1 & HF2).
  pose proof HZ as (Z1 & Z2). rewrite Z1 in HF1. rewrite Z2 in HF2.
  pose proof HG as (HC & Hro & _ & _ & _ & HL & _). pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  set (cap := wcap (crt_tree t) true) in *.
  set (w := wdoc (crt_tree t) true) in *.
  assert (Hwl : wlen (crt_tree t) true + 1 <= 2 ^ 28).
  { unfold wlen in *. pose proof (crt_len t) as H1. lia. }
  pose proof (RttModel.wcap_ge (crt_tree t) true ltac:(lia)) as Hcap.
  destruct (RttModel.wcap_pow (crt_tree t) true ltac:(lia)) as (j & Hj & Ecap).
  fold cap in Hcap, Ecap. unfold wlen in Hwl, Hcap. fold w in Hwl, Hcap.
  assert (Hqn : In (q, cap) ((q, cap) :: Do)) by (left; reflexivity).
  pose proof (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG Hqn) as Hq.
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ _ _ HM HL Hq) as (Hq1 & Hq2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & HFB). rewrite Forall_forall in HFB.
  destruct (HFB (q, cap) Hq) as (_ & Hqb & _). cbn [fst snd] in Hqb.
  pose proof (crt_blk_align L A mem md _ _ HM Hqb) as Hal.
  set (n0 := (- (q + Z.of_nat (length (map (Z_to_bv 8) w)) + 1)) mod 8).
  assert (Hn0 : 0 <= n0 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hfit : q + Z.of_nat (length w) + 1 + n0 <= q + cap).
  { unfold n0. rewrite length_map. Z.div_mod_to_equations. lia. }
  destruct (crt_bytes_of_present mem (q + Z.of_nat (length w) + 1) (Z.to_nat n0) ltac:(lia) ltac:(lia))
    as (slack & Hsl & HS).
  { intros i Hi. replace (q + Z.of_nat (length w) + 1 + i) with (q + (Z.of_nat (length w) + 1 + i)) by lia.
    apply (ledger_block_present B API L A mem md Lam peak cnt _ q cap _ HM HL Hq). lia. }
  unfold segs in HB, Hro, HF1, HF2. rewrite HSEG in HB, Hro, HF1, HF2.
  assert (HBT : bytes_at rsegs mem q (map (Z_to_bv 8) w ++ Z_to_bv 8 0 :: slack)).
  { rewrite map_app in HB. cbn [map] in HB.
    replace (map (Z_to_bv 8) w ++ Z_to_bv 8 0 :: slack) with ((map (Z_to_bv 8) w ++ [Z_to_bv 8 0]) ++ slack)
      by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (bytes_at_app rsegs mem q _ _)). split; [exact HB|].
    rewrite length_app, length_map. cbn [length]. replace (q + Z.of_nat (length w + 1)) with
      (q + Z.of_nat (length w) + 1) by lia. exact HS. }
  assert (Hnz : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) w)).
  { intros Hin. apply in_map_iff in Hin as (c & Ec & Hcin). rewrite Forall_forall in HFw.
    pose proof (HFw c Hcin) as Hr. apply (f_equal bv_unsigned) in Ec.
    rewrite !Z_to_bv_unsigned, !bv_wrap_small in Ec by (unfold bv_modulus; cbn; lia). lia. }
  eapply (crt_kAn fx regs _ mem md _ cpost Hh Hz Hro).
  { unfold rmk. rewrite G10, G18.
    apply (crt_w HROc HSL (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem) q (map (Z_to_bv 8) w) slack).
    - lia.
    - exact (bytes_at_normalize rsegs mem _ _ Hro HF2).
    - exact (bytes_at_normalize rsegs mem _ _ Hro HF1).
    - exact (bytes_at_normalize rsegs mem _ _ Hro HBT).
    - exact Hnz.
    - rewrite Hsl. fold n0. rewrite Z2Nat.id by lia. lia.
    - exact (mem_inv_normalize rsegs mem). }
  { intros ms0 (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' m0 regs' HQ HR Hsame HGr.
  destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _).
  crt_inj E R pc' m0.
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (munch_rel rsegs _ mem _ mem' m' HR0 HR Hsame MU) as MU'.
  pose proof (wmono_rel rsegs mem _ mem' m' HR0 HR Hsame WM) as WM'.
  pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as Hro'.
  rewrite <- HSEG in WM', Hro'.
  assert (HO : forall z, 0 <= z < 2 ^ 64 -> ~ (SP - CRT_K <= z < SP - 256) -> Frame.outside [] z)
    by (intros; exact I).
  pose proof (gi_munch _ _ _ _ _ _ _ _ _ _ _ _ HG MU' WM' Hro' HO) as HG'.
  change (Z_to_bv 64 0x13a04) with (Z_to_bv 64 PARSE_NOTING).
  apply (stpp fx L A regs' mem' md Lam peak cnt b Do q ms cset HZ Ht HG').
  - apply (pj_node_munch segs [] mem (lin Lam) mem' (lin Lam) _ _ _ HNo).
    + intros a k Hak. apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG). right. exact Hak.
    + exact MU'.
    + intros; exact I.
  - unfold segs. rewrite HSEG.
    apply (crt_bytes_frame rsegs mem mem' q _ HB).
    intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
    apply (mbyte_munch rsegs [] mem mem' (q + i) MU'); [lia | exact I].
  - exact HFw.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite HGr. unfold wlen. fold w. rewrite length_map. reflexivity.
  - rewrite HGr. transitivity (Z_to_bv 64 (bv_unsigned (getr regs 2) + 112)); [reflexivity|].
    rewrite G2, crt_uns by lia. reflexivity.
  - rewrite HGr. exact G8.
  - rewrite HGr. reflexivity.
  - rewrite HGr. reflexivity.
  - rewrite HGr. exact G19.
  - split; [rewrite HGr; exact G2|]. split; [rewrite HGr; exact G3|]. split; [rewrite HGr; exact G4|].
    split; [rewrite HGr; exact G26 | rewrite HGr; exact G27].
  - exact Hcnt.
  - exact Hcs.
  - exact Hcs0.
  - exact HRR.
  - exact Hfin.
Qed.

Lemma st4 : forall fx L A regs mem md Lam peak cnt b Do ms cset Df,
  ro = 0 /\ oo = 0 ->
  t = JObj ms ->
  gi fx L A mem md Lam peak cnt b Do ->
  pj_node segs mem (lin Lam) (SP - 256) (crt_tree t) Do ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 doc ->
  getr regs 19 = Z_to_bv 64 (Z.of_nat (length ms)) -> rbase regs ->
  cnt = cnt_r2 + 1 + cset -> 0 <= cset <= 3 -> (In MOD_AT (map fst ms) -> cset = 0) ->
  crt_dl (PjRoundTrip.ttrace t) Df ->
  crt_set_res F (rf_malloc F (crt_b2 F b0 cnt0 t Df) 37) (Z.of_nat (length ms)) (PjRoundTrip.ttrace t) b cset Do ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x1409c) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt b Do ms cset Df HZ Ht HG HNo G10 G8 G19 (G2 & G3 & G4 & G26 & G27)
    Hcnt Hcs Hcs0 HDf Hset.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof (crt_count_le t cset Hcs) as Hcl0. pose proof crt_m_le as Hm0.
  pose proof crt_tdep as (_ & Hdo).
  pose proof (gi_flags _ _ _ _ _ _ _ _ _ _ HG) as (HF1 & HF2).
  pose proof HZ as (Z1 & Z2). rewrite Z1 in HF1. rewrite Z2 in HF2.
  unfold segs in HF1, HF2. rewrite HSEG in HF1, HF2.
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  assert (Hwl : wlen (crt_tree t) true + 1 <= 2 ^ 28).
  { unfold wlen in *. pose proof (crt_len t) as H1. lia. }
  destruct (HOBJ ms Ht Df HDf) as (_ & _ & HR3).
  destruct (HR3 b cset Do Hset) as (HWR & HRR).
  assert (Ec : crt_count t cset = cnt_r2 - cnt0 + 1 + cset + wcalls (crt_tree t) true +
      Z.of_nat (PjRoundTrip.tcalls (crt_tree t))).
  { unfold crt_count, cnt_r2, cnt_r1. rewrite Ht. cbv beta iota. lia. }
  assert (Hwc : 0 <= wcalls (crt_tree t) true) by (unfold wcalls; lia).
  assert (HKW0 : 0 <= kw (crt_tree t) <= CRT_K - 256).
  { destruct (HKW (crt_tree t) Hdo) as [K1 K2].
    assert (HK : PJ_PARSE_K <= CRT_K - 256) by (unfold CRT_K; apply Z.leb_le; vm_compute; reflexivity). lia. }
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x140cc) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (Z_to_bv 64 1) (getr regs 2) (Z_to_bv 64 1) (getr regs 12)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (Z_to_bv 64 CRT_S2) (getr regs 19)
        (Z_to_bv 64 1) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x15f58 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. rewrite G10. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_set HROc (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem HF2 HF1).
    - intros ms0 E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs1 (-> & -> & ->) Hg.
  assert (H2 : getr regs1 2 = Z_to_bv 64 (SP - 256)) by (rewrite Hg; exact G2).
  assert (H4 : getr regs1 4 = getr regs0 4) by (rewrite Hg; exact G4).
  assert (H1 : getr regs1 1 = Z_to_bv 64 0x140cc) by (rewrite Hg; reflexivity).
  assert (Hra : YK0s.ret_ok (getr regs1 1)) by (rewrite H1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Hs : spZ regs1 = SP - 256) by (unfold spZ; rewrite H2; apply crt_uns; lia).
  assert (HDo : forall bk, In bk Do -> In bk Lam)
    by (intros bk Hb; apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); exact Hb).
  change (Z_to_bv 64 0x15f58) with (Z_to_bv 64 PJ_WRITE).
  eapply SR_bind.
  { apply (HW fx L A regs1 mem md (SP - 256) 1 (crt_tree t) Do Lam peak cnt (2 ^ 64 - 1) b).
    - exact (crt_renv fx L A mem md Lam peak cnt b _ regs1 _ HG H2 H4 Hra HKW0).
    - exact Hin.
    - exact HL.
    - exact Hres.
    - rewrite Hg. exact G2.
    - rewrite Hg. reflexivity.
    - lia.
    - exact HNo.
    - exact HDo.
    - left. lia.
    - exact Hwl.
    - lia.
    - change (negb (1 =? 0)) with true. rewrite Hcnt. exact HWR.
    - try change (negb (1 =? 0)) with true. lia. }
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & q & b2 & -> & FZ2 & FK2 & RP2 & RD2 &
    LG2 & Hpk2 & RS2 & G10' & HNo2 & Hfull & _).
  try change (negb (1 =? 0)) with true in *.
  destruct (Hfull ltac:(right; lia)) as (Hq0 & Hcnt2 & Hf2 & Eb2 & HPm & HNB2 & HFw & HB2).
  rewrite Hf2 in LG2.
  destruct (rpost_cstep B API _ L A regs1 mem md _ _ L2 A2 regs2 mem2 md2 RP2) as [HC2 HR].
  pose proof RP2 as (_ & _ & _ & _ & Hin' & _).
  rewrite Hs in HC2.
  assert (HG' : gi fx2 L2 A2 mem2 md2 Lam2 peak2 cnt2 b2 ((q, wcap (crt_tree t) true) :: Do)).
  { apply (gi_step fx fx2 L A mem md Lam peak cnt b _ (SP - 256) (kw (crt_tree t)) alloc_statics
             (fun _ _ => False) L2 A2 mem2 md2 Lam2 peak2 cnt2 b2 _ HG HC2).
    - lia.
    - lia.
    - intros a X. right. left. exact X.
    - intros a k _ Hf. exact Hf.
    - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    - intros a Ha X. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
    - exact (proj1 RD2).
    - apply Hin'. exact Hin.
    - exact FZ2.
    - intros r Hr. rewrite (FK2 r Hr). exact (Hfk r Hr).
    - exact LG2.
    - exact Hpk2.
    - cbn [app]. apply (Permutation_trans HPm). apply perm_skip. exact HP.
    - intros a k Hak. destruct Hak as [E|Y].
      + injection E as <- <-. intros Hb. apply (HNB2 q (wcap (crt_tree t) true) (or_introl eq_refl)).
        exact (HPers _ _ Hb (fun z => z)).
      + exact (HNB a k Y).
    - exact RS2. }
  assert (E5 : crt_b5 F b (crt_cnt2 cnt0 t + 1 + cset) t = b2) by (rewrite Eb2, Hcnt; reflexivity).
  rewrite H1.
  apply (st5 fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 b2 Do q ms cset HZ Ht HG' HNo2 HB2 HFw G10').
  - rewrite <- G8. transitivity (getr regs1 8); [apply (HR 8); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - transitivity (getr regs1 18); [apply (HR 18); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - rewrite <- G19. transitivity (getr regs1 19); [apply (HR 19); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - split; [rewrite <- G2; transitivity (getr regs1 2); [apply (HR 2); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G3; transitivity (getr regs1 3); [apply (HR 3); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G4; transitivity (getr regs1 4); [apply (HR 4); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G26; transitivity (getr regs1 26); [apply (HR 26); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    rewrite <- G27; transitivity (getr regs1 27); [apply (HR 27); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - rewrite Hcnt2, Ec. unfold cnt_r2, cnt_r1 in *. lia.
  - exact Hcs.
  - exact Hcs0.
  - rewrite <- E5. exact HRR.
  - intros Dk Dk' Do' Hk1 Hk2 Hk3.
    apply (crt_fin_obj b0 cnt0 t ms cset _ Df b Do Dk Dk' Do' Ht HDf Hset Hk1 Hk2 Hk3).
    rewrite E5. reflexivity.
Qed.

Lemma crt_r2_le : forall u, wcalls u false + Z.of_nat (PjRoundTrip.tcalls u) + wcalls u true +
  Z.of_nat (PjRoundTrip.tcalls u) <= crt_count u 0.
Proof. intros u. unfold crt_count. destruct u; cbv beta iota; unfold wcalls; lia. Qed.

Lemma crt_tag_range : forall u, 0 <= tag u <= 6.
Proof. intros u. destruct u; cbn [tag]; lia. Qed.

Lemma crt_tag6 : forall u, tag u = 6 -> exists ms, u = JObj ms.
Proof. intros u H. destruct u; cbn [tag] in H; try discriminate H. eexists. reflexivity. Qed.

Lemma crt_tree_id : forall u, tag u <> 6 -> crt_tree u = u.
Proof. intros u H. destruct u; try reflexivity. exfalso. apply H. reflexivity. Qed.

Lemma crt_count_id : forall u cset, tag u <> 6 ->
  crt_count u cset = wcalls u false + Z.of_nat (PjRoundTrip.tcalls u) + wcalls u true +
    Z.of_nat (PjRoundTrip.tcalls u).
Proof.
  intros u cset H. unfold crt_count.
  destruct u; try (exfalso; apply H; reflexivity); cbv beta iota; lia.
Qed.

Lemma crt_stamp_ok : Forall (fun c => 0 < c < 256) STAMP.
Proof. unfold STAMP. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma crt_stamp_nz : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) STAMP).
Proof.
  intros Hin. apply in_map_iff in Hin as (c & Ec & Hcin). pose proof crt_stamp_ok as HF.
  rewrite Forall_forall in HF. pose proof (HF c Hcin) as Hr. apply (f_equal bv_unsigned) in Ec.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small in Ec by (unfold bv_modulus; cbn; lia). lia.
Qed.

Lemma crt_stamp_ro : forall i, 0 <= i < 20 + 1 -> ro_addr segs (Z_to_bv 64 (STAMP_A + i)) = true.
Proof.
  intros i Hi. unfold segs. rewrite HSEG.
  assert (C : forallb (fun j => ro_addr rsegs (Z_to_bv 64 (STAMP_A + Z.of_nat j))) (seq 0 21) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. exact C.
Qed.

Lemma crt_set_len3 : forall n cap kl, (length (set_trace n cap kl) <= 3)%nat.
Proof. intros n cap kl. unfold set_trace. destruct (n =? cap); cbn; lia. Qed.

Lemma crt_obj_view : forall L A mem md Lam peak cnt fail p ms Dx, MR L A mem md ->
  ledger B L A mem Lam peak cnt fail -> pj_node segs mem (lin Lam) p (JObj ms) Dx ->
  exists num str kids keys n cap, pj_hdr segs mem p 6 num str kids keys n cap /\ n = Z.of_nat (length ms) /\
    n <= cap <= 2 ^ 54.
Proof.
  intros L A mem md Lam peak cnt fail p ms Dx HM HL H. cbn [pj_node] in H.
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & (_ & En & Hnc & Hcp & _)).
  exists num, str, kids, keys, n, cap. split; [exact Hh|]. split; [exact En|]. split; [exact Hnc|].
  destruct Hcp as [(-> & _ & _) | (Hc0 & Hk & _)]; [lia|].
  unfold lin in Hk. destruct (ledger_block_range B API L A mem md Lam peak cnt fail kids (56 * cap) HM HL Hk) as (H1 & H2 & _).
  pose proof alloc_ceiling_value. lia.
Qed.

Definition crt_mslack : list byte :=
  map (fun i => match seg_rom rsegs (Z_to_bv 64 (MOD_AT_A + 11 + Z.of_nat i)) with Some bb => bb
                | None => Z_to_bv 8 0 end) (seq 0 7).

Lemma crt_modat_full : forall m, mem_inv rsegs m ->
  bytes_at rsegs m MOD_AT_A (map (Z_to_bv 8) MOD_AT ++ Z_to_bv 8 0 :: crt_mslack).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold MOD_AT_A; lia | apply Z.leb_le; vm_compute; reflexivity |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma crt_modat_nz : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) MOD_AT).
Proof.
  intros Hin. apply in_map_iff in Hin as (c & Ec & Hcin). pose proof crt_modat_ok as HF.
  rewrite Forall_forall in HF. pose proof (HF c Hcin) as Hr. apply (f_equal bv_unsigned) in Ec.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small in Ec by (unfold bv_modulus; cbn; lia). lia.
Qed.

Lemma crt_modat_ro : forall i, 0 <= i < 10 + 1 + 7 -> ro_addr segs (Z_to_bv 64 (MOD_AT_A + i)) = true.
Proof.
  intros i Hi. unfold segs. rewrite HSEG.
  assert (C : forallb (fun j => ro_addr rsegs (Z_to_bv 64 (MOD_AT_A + Z.of_nat j))) (seq 0 18) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. exact C.
Qed.

Lemma crt_modat_inimg : forall y, MOD_AT_A <= y < MOD_AT_A + 10 + 1 -> in_img B y.
Proof.
  intros y Hy. unfold in_img. rewrite HSEG.
  split; [intros E; apply (f_equal (@length Segment)) in E; vm_compute in E; discriminate E|].
  assert (C1 : existsb (fun r => (bv_unsigned (fst r) <=? MOD_AT_A) &&
                 (MOD_AT_A + 11 <=? bv_unsigned (fst r) + bv_unsigned (snd r))) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in C1 as (r1 & H1 & E1). apply andb_prop in E1 as [E1 F1]. apply Z.leb_le in E1, F1.
  exists r1. split; [assumption | lia].
Qed.

Lemma crt_foot_img : forall L A mem Lam peak cnt fail p Dc y, ledger B L A mem Lam peak cnt fail ->
  (forall bk, In bk Dc -> In bk Lam) -> pj_foot p Dc y -> in_img B y -> p <= y < p + 56.
Proof.
  intros L A mem Lam peak cnt fail p Dc y HL HD [Hy|([ba bk] & Hb & Hy)] Hi; [exact Hy|].
  exfalso. destruct HL as (_ & _ & _ & _ & _ & HF). rewrite Forall_forall in HF.
  destruct (HF (ba, bk) (HD _ Hb)) as (_ & _ & _ & Himg). cbn [fst snd] in Himg. unfold pj_holds in Hy.
  cbn [fst snd] in Hy. apply (Himg (y - (ba - 16))); [lia|]. replace (ba - 16 + (y - (ba - 16))) with y by lia.
  exact Hi.
Qed.

Lemma st3 : forall fx L A regs mem md Lam peak cnt Db Df a ms,
  ro = 0 /\ oo = 0 ->
  t = JObj ms ->
  gi fx L A mem md Lam peak cnt (rf_malloc F (crt_b2 F b0 cnt0 t Df) 37) ((a, 21) :: Db) ->
  pj_node segs mem (lin Lam) (SP - 256 + 56) (JStr STAMP) [(a, 21)] ->
  pj_node segs mem (lin Lam) (SP - 256) t Db ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 doc ->
  getr regs 19 = Z_to_bv 64 (Z.of_nat (length ms)) -> rbase regs ->
  cnt = cnt_r2 + 1 -> crt_dl (PjRoundTrip.ttrace t) Df -> crt_dl (PjRoundTrip.ttrace t) Db ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x1407c) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt Db Df a ms HZ Ht HG HNs HNb G10 G8 G19 (G2 & G3 & G4 & G26 & G27) Hcnt
    HDf HDbl.
  destruct (HOBJ ms Ht Df HDf) as (_ & HR2 & _).
  set (b := rf_malloc F (crt_b2 F b0 cnt0 t Df) 37) in *.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof crt_m_le as Hm0. pose proof (crt_r2_le t) as Hr2.
  pose proof (crt_count_le t 0 ltac:(lia)) as Hcl0.
  pose proof crt_tdep as (Hdt & _).
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  pose proof HL as (_ & _ & Hcn & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  assert (Hwc : 0 <= wcalls (crt_tree t) true) by (unfold wcalls; lia).
  rewrite Ht in HNb.
  destruct (crt_obj_view L A mem md Lam peak cnt _ (SP - 256) ms Db HM HL HNb)
    as (num & str & kids & keys & nn & cap & HH & Enn & Hcap).
  assert (Hro0 : ro_agree rsegs mem) by (unfold segs in Hro; rewrite HSEG in Hro; exact Hro).
  pose proof (gi_nodup _ _ _ _ _ _ _ _ _ _ HG) as HND. cbn [map fst] in HND.
  assert (Hnd : ~ In (a, 21) Db).
  { intros Hb. apply (proj1 (NoDup_cons_iff a _) HND). exact (in_map fst _ _ Hb). }
  assert (HDb : forall bk, In bk Db -> In bk Lam)
    by (intros bk Hb; apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); right; exact Hb).
  assert (HDa : In (a, 21) Lam) by (apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG); left; reflexivity).
  assert (HDB' : forall bk, In bk (Db ++ [(a, 21)]) -> In bk Lam)
    by (intros bk Hb; destruct (in_app_or _ _ _ Hb) as [Y|[<-|[]]]; [exact (HDb _ Y) | exact HDa]).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ a 21 HM HL HDa) as (Ha1 & Ha2 & _).
  assert (Hkl : Z.of_nat (length (map (Z_to_bv 8) MOD_AT)) = 10) by (rewrite length_map; reflexivity).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x1409c) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 2) (Z_to_bv 64 MOD_AT_A)
        (Z_to_bv 64 (bv_unsigned (getr regs 2) + 56))
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x15d7c /\ mem' = mem) _ Hh Hz).
  { unfold rmk. rewrite G10. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_ps (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms0 E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs1 (-> & -> & ->) Hg.
  assert (H2 : getr regs1 2 = Z_to_bv 64 (SP - 256)) by (rewrite Hg; exact G2).
  assert (H4 : getr regs1 4 = getr regs0 4) by (rewrite Hg; exact G4).
  assert (H1 : getr regs1 1 = Z_to_bv 64 0x1409c) by (rewrite Hg; reflexivity).
  assert (Hra : YK0s.ret_ok (getr regs1 1)) by (rewrite H1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Hs : spZ regs1 = SP - 256) by (unfold spZ; rewrite H2; apply crt_uns; lia).
  assert (HK : 0 <= PJ_SET_K 32%nat <= CRT_K - 256) by (unfold CRT_K; split; apply Z.leb_le; vm_compute; reflexivity).
  pose proof (crt_modat_full _ (mem_inv_normalize rsegs mem)) as HMd.
  apply (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ (mem_rel_normalize rsegs mem Hro0))) in HMd.
  change (Z_to_bv 64 0x15d7c) with (Z_to_bv 64 PJ_SET).
  eapply SR_bind.
  { apply (HSET fx L A regs1 mem md Lam peak cnt (2 ^ 64 - 1) b (SP - 256) MOD_AT_A (SP - 256 + 56) ms (JStr STAMP)
      Db [(a, 21)] num str kids keys nn cap (map (Z_to_bv 8) MOD_AT) crt_mslack 32%nat).
    - exact (crt_renv fx L A mem md Lam peak cnt b _ regs1 _ HG H2 H4 Hra HK).
    - exact HL.
    - exact Hres.
    - rewrite Hg. exact G2.
    - rewrite Hg. reflexivity.
    - rewrite Hg. transitivity (Z_to_bv 64 (bv_unsigned (getr regs 2) + 56)); [reflexivity|].
      rewrite G2, crt_uns by lia. reflexivity.
    - lia.
    - exact HNb.
    - exact HH.
    - lia.
    - exact (crt_rplace fx L A mem md Lam peak cnt b _ regs1 (SP - 256) HG Hs ltac:(lia) ltac:(lia)).
    - lia.
    - exact HNs.
    - exact (crt_rplace fx L A mem md Lam peak cnt b _ regs1 (SP - 256 + 56) HG Hs ltac:(lia) ltac:(lia)).
    - intros bk [<-|[]] Hb. exact (Hnd Hb).
    - intros y Hy Hf. destruct (gi_foot _ _ _ _ _ _ _ _ _ _ (SP - 256) Db y HG HDb Hf); lia.
    - intros bb y [<-|[]] Hy. unfold pj_holds in Hy. cbn [fst snd] in Hy. lia.
    - rewrite <- Ht. lia.
    - cbn [depth]. lia.
    - unfold segs. rewrite HSEG. exact HMd.
    - exact crt_modat_nz.
    - apply Z.leb_le. vm_compute. reflexivity.
    - left. rewrite Hkl.
      assert (E7 : Z.of_nat (length crt_mslack) = 7) by (unfold crt_mslack; rewrite length_map, length_seq; reflexivity).
      rewrite E7. exact crt_modat_ro.
    - rewrite Hkl. intros y Hy. pose proof (crt_modat_inimg y Hy) as Himg. unfold MOD_AT_A in Hy.
      split; intros Hf.
      + destruct (crt_foot_img L A mem Lam peak cnt _ (SP - 256) Db y HL HDb Hf Himg). lia.
      + assert (HDa1 : forall bk, In bk [(a, 21)] -> In bk Lam) by (intros bk [<-|[]]; exact HDa).
        destruct (crt_foot_img L A mem Lam peak cnt _ (SP - 256 + 56) [(a, 21)] y HL HDa1 Hf Himg). lia.
    - rewrite Hs, Hkl. cbn [Frame.disjoint_from]. unfold MOD_AT_A, CRT_K in *.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    - unfold cnt_r2, cnt_r1 in Hcnt. lia.
    - rewrite Hkl, Enn. apply HR2. lia. }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & fail2 & res & c & Lr & Do & -> & RP2 & RD2 & G10' & LG2 &
    Hfa & HP1 & HP2 & HZw & Hres0 & Arms).
  rewrite (crt_zb MOD_AT crt_modat_ok) in Arms.
  rewrite Hkl in Arms.
  pose proof (crt_set_len3 nn cap 10) as Hl3.
  assert (Hcl : (c <= 3)%nat /\ (In MOD_AT (map fst ms) -> c = 0%nat) /\ peak <= peak2 /\
      (forall bk, In bk Do -> In bk Db \/ bk = (a, 21) \/ ~ In (fst bk - 16, snd bk + 16) (blocks L A)) /\
      pj_node segs mem2 (lin Lam2) (SP - 256) (crt_tree t) Do /\
      exists b4, rf_ok F A2 b4 /\ crt_set_res F b nn (PjRoundTrip.ttrace t) b4 (Z.of_nat c) Do).
  { destruct Arms as [Arm1|[Arm2|Arm3]].
    - destruct Arm1 as (Hinm & Ec & Er & Epk & HX1 & HNo2).
      destruct HX1 as (i & vi & Di & Dr & _ & _ & _ & HPD & HPDo & (Di' & HPi & Hres') & _).
      subst c.
      split; [lia|]. split; [intros _; reflexivity|]. split; [lia|].
      split.
      { intros bk Hb. apply (Permutation_in _ HPDo) in Hb. destruct (in_app_or _ _ _ Hb) as [Y|[<-|[]]].
        + left. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Y.
        + right. left. reflexivity. }
      split; [rewrite Ht; exact HNo2|].
      exists (rf_frees F b Di'). split; [exact Hres'|].
      exists Db. split; [exact HDbl|]. left. split; [reflexivity|].
      exists Di, Dr, Di', a. split; [exact HPD|]. split; [exact HPi|]. split; [reflexivity | exact HPDo].
    - destruct Arm2 as (Hnin & _ & Ec & Er & Epk & Hres' & _ & _ & HX1 & HNo2).
      destruct HX1 as (Dold & Dnew & Dr & a' & HPD & HPDo & HNBn & Hcases). subst c.
      assert (Hold : forall bk, In bk Dold -> In bk Db)
        by (intros bk Hb; apply (Permutation_in _ (Permutation_sym HPD)); apply in_or_app; left; exact Hb).
      split; [lia|]. split; [intros X; contradiction|]. split; [rewrite Epk; lia|].
      split.
      { intros bk Hb. apply (Permutation_in _ HPDo) in Hb. destruct (in_app_or _ _ _ Hb) as [Y|[E|Y]].
        + destruct bk as [x1 k]. destruct (HNBn x1 k (in_or_app _ _ _ (or_introl Y))) as [Z|Z];
            [left; exact (Hold _ Z) | right; right; exact Z].
        + subst bk.
          destruct (HNBn a' (10 + 1) (in_or_app Dnew [(a', 10 + 1)] (a', 10 + 1) (or_intror (or_introl eq_refl))))
            as [Z|Z]; [left; exact (Hold _ Z) | right; right; exact Z].
        + destruct (in_app_or _ _ _ Y) as [Z|[<-|[]]].
          * left. apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. exact Z.
          * right. left. reflexivity. }
      split; [rewrite Ht; exact HNo2|].
      exists (rf_run F b (set_trace nn cap 10)). split; [exact Hres'|].
      exists Db. split; [exact HDbl|]. right.
      exists cap, Dold, Dnew, Dr, a, a'. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HPD|]. split; [exact HPDo|].
      destruct Hcases as [(Hlt & -> & ->)|(Heq & -> & k' & y' & ->)].
      + left. split; [exact Hlt|]. split; reflexivity.
      + right. split; [exact Heq|].
        split; [unfold kids_blk, keys_blk; destruct (cap =? 0); reflexivity | reflexivity].
    - exfalso. destruct Arm3 as (_ & Hst & _). unfold cnt_r2, cnt_r1 in Hcnt. lia. }
  destruct Hcl as (Hc3 & Hcs0 & Hpk2 & HDo & HNo2 & b4 & Hres4 & Hset).
  assert (Hcb : cnt + 3 < 2 ^ 64 - 1) by (unfold cnt_r2, cnt_r1 in Hcnt; lia).
  assert (Er : res = 0) by (apply Hres0; right; lia). subst res.
  assert (Hf2 : fail2 = 2 ^ 64 - 1) by (apply (proj2 Hfa); lia). subst fail2.
  assert (HLr : Permutation Lr Lam0).
  { apply (Permutation_app_inv_l (Db ++ [(a, 21)])). rewrite <- app_assoc.
    apply (Permutation_trans (Permutation_sym HP1)). apply (Permutation_trans HP).
    apply Permutation_app_tail. cbn [app]. apply Permutation_cons_append. }
  destruct (rpost_cstep B API _ L A regs1 mem md _ _ L2 A2 regs2 mem2 md2 RP2) as [HC2 HR].
  pose proof RP2 as (_ & _ & _ & _ & Hin' & _).
  rewrite Hs in HC2.
  assert (HG' : gi fx L2 A2 mem2 md2 Lam2 peak2 (cnt + Z.of_nat c) b4 Do).
  { apply (gi_step fx fx L A mem md Lam peak cnt b _ (SP - 256) (PJ_SET_K 32)
             (pj_set_writes (SP - 256) (SP - 256 + 56) Db [(a, 21)]) (freed (Db ++ [(a, 21)]))
             L2 A2 mem2 md2 Lam2 peak2 _ _ _ HG HC2).
    - unfold CRT_K in *. lia.
    - lia.
    - intros z [X|[X|[(ba & bk & Hb & Hr)|X]]]; [left; lia | left; lia | | right; left; exact X].
      right. right. exists ba, bk. split; [|exact Hr].
      destruct (in_app_or _ _ _ Hb) as [Y|[E|[]]]; [right; exact Y | left; exact E].
    - intros z k Hb Hf. unfold freed in Hf. apply (HNB (z + 16) (k - 16)).
      + destruct (in_app_or _ _ _ Hf) as [Y|[E|[]]]; [right; exact Y | left; exact E].
      + replace (z + 16 - 16) with z by lia. replace (k - 16 + 16) with k by lia. exact Hb.
    - intros z Hzz. destruct (Z_lt_le_dec z (SP - 256 + 112)) as [X|X].
      + left. destruct (Z_lt_le_dec z (SP - 256 + 56)) as [Y|Y]; [left; lia | right; left; lia].
      + right. intros [Y|[Y|[(ba & bk & Hb & Hr)|Y]]]; [lia | lia | |
          unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Y; lia].
        destruct (ledger_block_range B API L A mem md Lam peak cnt _ ba bk HM HL (HDB' _ Hb)). lia.
    - intros z Hzz [X|[X|[(ba & bk & Hb & Hr)|X]]].
      + exact (crt_node_wr _ _ _ _ _ HNo2 z X).
      + destruct HZw as ((_ & _ & _ & Hw) & _). exact (proj1 (Hw z X)).
      + destruct (ledger_block_range B API L A mem md Lam peak cnt _ ba bk HM HL (HDB' _ Hb)). lia.
      + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
    - exact (proj1 RD2).
    - apply Hin'. exact Hin.
    - exact Hfz.
    - exact Hfk.
    - exact LG2.
    - exact Hpk2.
    - exact (Permutation_trans HP2 (Permutation_app_head Do HLr)).
    - intros x0 k Hx0 Hb. destruct (HDo (x0, k) Hx0) as [Y|[E|Y]].
      + exact (HNB x0 k (or_intror Y) Hb).
      + injection E as -> ->. exact (HNB a 21 (or_introl eq_refl) Hb).
      + apply Y. cbn [fst snd]. exact (HPers _ _ Hb (fun w => w)).
    - exact Hres4. }
  rewrite H1.
  apply (st4 fx L2 A2 regs2 mem2 md2 Lam2 peak2 _ b4 Do ms (Z.of_nat c) Df HZ Ht HG' HNo2 G10').
  - rewrite <- G8. transitivity (getr regs1 8); [apply (HR 8); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - rewrite <- G19. transitivity (getr regs1 19); [apply (HR 19); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - split; [rewrite <- G2; transitivity (getr regs1 2); [apply (HR 2); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G3; transitivity (getr regs1 3); [apply (HR 3); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G4; transitivity (getr regs1 4); [apply (HR 4); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G26; transitivity (getr regs1 26); [apply (HR 26); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    rewrite <- G27; transitivity (getr regs1 27); [apply (HR 27); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - lia.
  - lia.
  - intros X. rewrite (Hcs0 X). reflexivity.
  - exact HDf.
  - rewrite <- Enn. exact Hset.
Qed.

Lemma st2 : forall fx L A regs mem md Lam peak cnt Db Df,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt (crt_b2 F b0 cnt0 t Df) Db ->
  pj_node segs mem (lin Lam) (SP - 256) t Db ->
  getr regs 8 = Z_to_bv 64 doc -> getr regs 10 = Z_to_bv 64 0 -> rbase regs ->
  cnt = cnt_r2 -> crt_dl (PjRoundTrip.ttrace t) Df -> crt_dl (PjRoundTrip.ttrace t) Db ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14058) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt Db Df HZ HG HNb G8 G10 (G2 & G3 & G4 & G26 & G27) Hcnt HDf HDbl.
  set (b := crt_b2 F b0 cnt0 t Df) in *.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof (crt_count_le t 0 ltac:(lia)) as Hcl0. pose proof crt_m_le as Hm0.
  pose proof crt_tdep as (Hdt & Hdo).
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  destruct (PjSame.pj_view segs mem (lin Lam) doc t D HN) as (num & str & kids & keys & nn & cap & HH & Hnn & _).
  destruct HH as (_ & (Ht0 & Hty) & _ & _ & _ & _ & (Hn0 & Hnb) & _).
  unfold segs in Hty, Hnb. rewrite HSEG in Hty, Hnb.
  assert (Hs8 : bv_unsigned (getr regs 8) = doc) by (rewrite G8; apply crt_uns; lia).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => mem' = mem /\
      ((tag t <> 6 /\ R = mkR (Z_to_bv 64 0x14250) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
          (getr regs 6) (getr regs 7) (getr regs 8) (Z_to_bv 64 0) (getr regs 2) (Z_to_bv 64 6) (getr regs 12)
          (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
          (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
          (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\ pc' = Z_to_bv 64 0x15c08) \/
       (tag t = 6 /\ R = mkR (Z_to_bv 64 0x1407c) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
          (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (Z_to_bv 64 (bv_unsigned (getr regs 2) + 56))
          (Z_to_bv 64 STAMP_A) (getr regs 12)
          (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (Z_to_bv 64 nn)
          (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
          (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\ pc' = Z_to_bv 64 0x15ef4)))
    _ Hh Hz).
  { unfold rmk. rewrite G10. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_r2 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (tag t) (Z_to_bv 64 nn)).
      + rewrite Hs8. exact Hty.
      + exact (crt_tag_range t).
      + rewrite Hs8. exact Hnb.
    - intros ms0 [(Hty6 & E)|(Hty6 & E)]; rewrite E; do 3 eexists; (split; [reflexivity|]);
        (split; [reflexivity|]); [left | right]; (split; [exact Hty6|]); split; reflexivity. }
  intros R pc' mem' regs1 (-> & [(Hty6 & -> & ->)|(Hty6 & -> & ->)]) Hg.
  - assert (Etr : crt_tree t = t) by exact (crt_tree_id t Hty6).
    pose proof (crt_count_id t 0 Hty6) as Ecn.
    apply (stpfc fx L A regs1 mem md Lam peak cnt b t Db 0 0 HG HNb Hdt).
    + rewrite Hg. reflexivity.
    + rewrite Hg. exact G2.
    + rewrite Hg. exact G3.
    + rewrite Hg. exact G4.
    + rewrite Hg. exact G2.
    + rewrite Hg. exact G26.
    + rewrite Hg. exact G27.
    + rewrite Hg. reflexivity.
    + intros Db' HPb. right. split; [reflexivity|]. split; [exact (proj1 HZ)|]. split; [exact (proj2 HZ)|].
      split; [rewrite Ecn, Hcnt; unfold cnt_r2, cnt_r1; lia|]. split; [lia|].
      split; [intros ms E; exfalso; apply Hty6; rewrite E; reflexivity|].
      exact (crt_fin_nobj b0 cnt0 t 0 _ Df Db Db' Hty6 HDf HDbl HPb eq_refl).
  - destruct (crt_tag6 t Hty6) as (ms & Ht).
    destruct (HOBJ ms Ht Df HDf) as (HR1 & _ & _).
    assert (Enn : nn = Z.of_nat (length ms))
      by (rewrite Hnn, Ht; cbn [PjSame.slots]; rewrite length_map; reflexivity).
    assert (H2 : getr regs1 2 = Z_to_bv 64 (SP - 256)) by (rewrite Hg; exact G2).
    assert (H4 : getr regs1 4 = getr regs0 4) by (rewrite Hg; exact G4).
    assert (H1 : getr regs1 1 = Z_to_bv 64 0x1407c) by (rewrite Hg; reflexivity).
    assert (Hra : YK0s.ret_ok (getr regs1 1)) by (rewrite H1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hs : spZ regs1 = SP - 256) by (unfold spZ; rewrite H2; apply crt_uns; lia).
    assert (HK : 0 <= PJ_STRING_K <= CRT_K - 256) by (unfold CRT_K; split; apply Z.leb_le; vm_compute; reflexivity).
    assert (Hro0 : ro_agree rsegs mem) by (unfold segs in Hro; rewrite HSEG in Hro; exact Hro).
    pose proof (crt_stamp_img _ (mem_inv_normalize rsegs mem)) as HSt.
    apply (proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ (mem_rel_normalize rsegs mem Hro0))) in HSt.
    rewrite map_app in HSt. cbn [map] in HSt.
    assert (Hlen : Z.of_nat (length (map (Z_to_bv 8) STAMP)) = 20) by (rewrite length_map; reflexivity).
    eapply SR_bind.
    { apply (HPS fx L A regs1 mem md Lam peak cnt (2 ^ 64 - 1) b (SP - 256 + 56) STAMP_A
        (map (Z_to_bv 8) STAMP) []).
      - exact (crt_renv fx L A mem md Lam peak cnt b _ regs1 _ HG H2 H4 Hra HK).
      - exact HL.
      - exact Hres.
      - rewrite Hg. rewrite G2, crt_uns by lia. reflexivity.
      - rewrite Hg. reflexivity.
      - lia.
      - split; [Z.div_mod_to_equations; lia|].
        apply (gi_stk_in _ _ _ _ _ _ _ _ _ _ _ _ HG); unfold CRT_K; lia.
      - exact (crt_rplace fx L A mem md Lam peak cnt b _ regs1 (SP - 256 + 56) HG Hs ltac:(lia) ltac:(lia)).
      - rewrite Hs. cbn [Frame.disjoint_from]. unfold CRT_K in HK. split; [lia | exact I].
      - right. split; [unfold STAMP_A; lia|].
        split; [unfold segs; rewrite HSEG; exact HSt|].
        split; [exact crt_stamp_nz|].
        split; [rewrite Hlen; unfold STAMP_A; reflexivity|].
        split; [left; rewrite Hlen; exact crt_stamp_ro|].
        rewrite Hlen. split; [cbn [Frame.disjoint_from]; unfold STAMP_A; split; [lia | exact I]|].
        rewrite Hs. cbn [Frame.disjoint_from]. unfold STAMP_A, CRT_K in *. split; [lia | exact I].
      - rewrite Hlen. lia.
      - rewrite Hlen. exact HR1. }
    intros c' (L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & fail2 & res & -> & RP2 & RD2 & G10' & LG2 & Arms).
    destruct Arms as [(_ & Hres0 & Hf2 & Hres' & a & -> & HNB2 & Hpk2 & HNs) | (Hcf & _)];
      [| exfalso; pose proof (crt_r2_le t) as Hr2; unfold cnt_r2, cnt_r1 in Hcnt; lia].
    subst res fail2.
    rewrite Hlen in HNs, HNB2, Hres', LG2, Hpk2. rewrite (crt_zb STAMP crt_stamp_ok) in HNs.
    replace ((cnt + 1) mod 2 ^ 64) with (cnt + 1) in LG2
      by (pose proof (crt_r2_le t) as Hr2; pose proof HL as (_ & _ & Hcn & _); unfold cnt_r2, cnt_r1 in Hcnt;
          rewrite Z.mod_small; [reflexivity | lia]).
    destruct (rpost_cstep B API _ L A regs1 mem md _ _ L2 A2 regs2 mem2 md2 RP2) as [HC2 HR].
    pose proof RP2 as (_ & _ & _ & _ & Hin' & _).
    rewrite Hs in HC2.
    assert (HG' : gi fx L2 A2 mem2 md2 ((a, 20 + 1) :: Lam) peak2 (cnt + 1)
        (rf_malloc F (crt_b2 F b0 cnt0 t Df) 37) ((a, 21) :: Db)).
    { apply (gi_step fx fx L A mem md Lam peak cnt b _ (SP - 256) PJ_STRING_K (pj_string_writes (SP - 256 + 56))
               (fun _ _ => False) L2 A2 mem2 md2 _ _ (cnt + 1) _ _ HG HC2).
      - unfold CRT_K in *. lia.
      - lia.
      - intros z [X|X]; [left; lia | right; left; exact X].
      - intros z k _ Hf. exact Hf.
      - intros z Hzz. unfold pj_string_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
      - intros z Hzz [X|X]; [exact (crt_node_wr _ _ _ _ _ HNs z X)|].
        unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
      - exact (proj1 RD2).
      - apply Hin'. exact Hin.
      - exact Hfz.
      - exact Hfk.
      - exact LG2.
      - rewrite Hpk2. lia.
      - cbn [app]. apply perm_skip. exact HP.
      - intros z k [E|Y].
        + injection E as <- <-. intros Hb. apply (HNB2 a 21 (or_introl eq_refl)). exact (HPers _ _ Hb (fun w => w)).
        + exact (HNB z k Y).
      - exact Hres'. }
    rewrite H1.
    apply (st3 fx L2 A2 regs2 mem2 md2 _ _ (cnt + 1) Db Df a ms HZ Ht HG' HNs).
    + rewrite Ht in HNb |- *.
      apply (gi_node fx L A mem md Lam peak cnt b _ (SP - 256) PJ_STRING_K (pj_string_writes (SP - 256 + 56))
        (fun _ _ => False) L2 A2 mem2 md2 _ (SP - 256) (JObj ms) Db HG HC2 HNb).
      * intros bk Hb. exact Hb.
      * intros bk Hb. right. apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG). exact Hb.
      * lia.
      * lia.
      * intros z Hzz. split; [unfold cwin; destruct crt_static as (_ & Herr & _); rewrite Herr;
          unfold strtod_c.STRTOD_ERRNO; unfold CRT_K in HK; lia|].
        intros [X|X]; [lia | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X; lia].
      * intros z k Hak. split; [intros Hf; exact Hf|]. intros i Hi [X|X].
        -- destruct (gi_blk_stat _ _ _ _ _ _ _ _ _ _ z k i HG Hak Hi) as (_ & X1 & _). lia.
        -- exact (proj1 (gi_blk_stat _ _ _ _ _ _ _ _ _ _ z k i HG Hak Hi) X).
    + exact G10'.
    + rewrite <- G8. transitivity (getr regs1 8); [apply (HR 8); unfold callee_saved; lia | rewrite Hg; reflexivity].
    + transitivity (getr regs1 19); [apply (HR 19); unfold callee_saved; lia | rewrite Hg, Enn; reflexivity].
    + split; [rewrite <- G2; transitivity (getr regs1 2); [apply (HR 2); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
      split; [rewrite <- G3; transitivity (getr regs1 3); [apply (HR 3); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
      split; [rewrite <- G4; transitivity (getr regs1 4); [apply (HR 4); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
      split; [rewrite <- G26; transitivity (getr regs1 26); [apply (HR 26); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
      rewrite <- G27; transitivity (getr regs1 27); [apply (HR 27); unfold callee_saved; lia | rewrite Hg; reflexivity].
    + lia.
    + exact HDf.
    + exact HDbl.
Qed.

Lemma st1 : forall fx L A regs mem md Lam peak cnt Db,
  ro = 0 /\ oo = 0 ->
  gi fx L A mem md Lam peak cnt (crt_b1 F b0 cnt0 t) Db ->
  pj_node segs mem (lin Lam) (SP - 256) t Db ->
  getr regs 8 = Z_to_bv 64 doc -> getr regs 10 = Z_to_bv 64 0 -> rbase regs ->
  cnt = cnt_r1 -> crt_dl (PjRoundTrip.ttrace t) Db ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14038) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak cnt Db HZ HG HNb G8 G10 (G2 & G3 & G4 & G26 & G27) Hcnt HDbl.
  set (b := crt_b1 F b0 cnt0 t) in *.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof (crt_count_le t 0 ltac:(lia)) as Hcl0. pose proof crt_m_le as Hm0. pose proof (crt_r2_le t) as Hr2.
  pose proof crt_tdep as (Hdt & _).
  pose proof HG as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _ & _ & _ & HPers & _).
  pose proof HL as (_ & _ & Hcn & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  assert (Hwl : wlen t true + 1 <= 2 ^ 28) by lia.
  assert (Hwc : 0 <= wcalls t true /\ 0 <= wcalls t false) by (unfold wcalls; lia).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (Z_to_bv 64 0x14058) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (Z_to_bv 64 1) (getr regs 8) (Z_to_bv 64 1) (Z_to_bv 64 0)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x14d88 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. rewrite G10. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_r1 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms0 E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs1 (-> & -> & ->) Hg.
  assert (H2 : getr regs1 2 = Z_to_bv 64 (SP - 256)) by (rewrite Hg; exact G2).
  assert (H4 : getr regs1 4 = getr regs0 4) by (rewrite Hg; exact G4).
  assert (H1 : getr regs1 1 = Z_to_bv 64 0x14058) by (rewrite Hg; reflexivity).
  assert (Hra : YK0s.ret_ok (getr regs1 1)) by (rewrite H1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Hs : spZ regs1 = SP - 256) by (unfold spZ; rewrite H2; apply crt_uns; lia).
  assert (HK : 0 <= RTT_K <= CRT_K - 256) by (unfold CRT_K; split; apply Z.leb_le; vm_compute; reflexivity).
  change (Z_to_bv 64 0x14d88) with (Z_to_bv 64 ROUND_TRIP_TEXT).
  eapply SR_bind.
  { apply (HRTT fx L A regs1 mem md Lam peak cnt b doc 1 0 t D 0 0).
    - exact (crt_renv fx L A mem md Lam peak cnt b _ regs1 _ HG H2 H4 Hra HK).
    - exact Hin.
    - exact HL.
    - unfold cnt_r1 in Hcnt. lia.
    - exact Hres.
    - rewrite Hg. exact G8.
    - rewrite Hg. reflexivity.
    - rewrite Hg. reflexivity.
    - right. reflexivity.
    - exact HN.
    - exact (gi_D _ _ _ _ _ _ _ _ _ _ HG).
    - lia.
    - lia.
    - eapply PjRoundTrip.wf_read. exact HX.
    - exact Hdt.
    - exact Hwl.
    - left. reflexivity.
    - change (negb (1 =? 0)) with true. rewrite Hcnt. exact HRM2.
    - lia.
    - lia.
    - pose proof (proj1 (gi_flags _ _ _ _ _ _ _ _ _ _ HG)) as X. rewrite (proj1 HZ) in X. exact X.
    - pose proof (proj2 (gi_flags _ _ _ _ _ _ _ _ _ _ HG)) as X. rewrite (proj2 HZ) in X. exact X. }
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & -> & FZ2 & FK2 & RR2 & RD2 & _ & _ & Harms).
  destruct Harms as [(Hbad & _) | (_ & _ & G10' & LG2 & Hpk2 & HN2 & Hc0 & _)];
    [exfalso; destruct Hbad as [X|X]; apply X; reflexivity|].
  try change (negb (1 =? 0)) with true in *.
  destruct (Hc0 eq_refl) as (HPm & Db2 & Df & HPbf & HLz & HNl & Hres').
  assert (HDf : crt_dl (PjRoundTrip.ttrace t) Df) by exact (crt_dl_perm _ Db2 Df HPbf (conj HLz HNl)).
  destruct (rtt_cstep B API _ regs1 _ L A mem md L2 A2 regs2 mem2 md2 RR2) as [HC2 HR].
  pose proof RR2 as (_ & _ & _ & Hin' & _).
  rewrite Hs in HC2.
  assert (HG' : gi fx2 L2 A2 mem2 md2 Lam2 peak2 (cnt + wcalls t true + Z.of_nat (PjRoundTrip.tcalls t))
      (crt_b2 F b0 cnt0 t Df) Db).
  { apply (gi_step fx fx2 L A mem md Lam peak cnt b _ (SP - 256) RTT_K (rtt_writes 0) NoG L2 A2 mem2 md2 Lam2
             peak2 _ (crt_b2 F b0 cnt0 t Df) _ HG HC2).
    - unfold CRT_K in *. lia.
    - lia.
    - intros a [(X & _)|X]; [exfalso; apply X; reflexivity | right; left; exact X].
    - intros a k _ Hf. exact Hf.
    - intros a Ha. unfold rtt_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    - intros a Ha [(X & _)|X]; [exfalso; apply X; reflexivity|].
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
    - exact (proj1 RD2).
    - apply Hin'. exact Hin.
    - exact FZ2.
    - intros r Hr. rewrite (FK2 r Hr). exact (Hfk r Hr).
    - exact LG2.
    - exact Hpk2.
    - exact (Permutation_trans HPm HP).
    - exact HNB.
    - rewrite Hcnt in Hres'. exact Hres'. }
  rewrite H1.
  apply (st2 fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 _ Db Df HZ HG').
  - apply (gi_node fx L A mem md Lam peak cnt b _ (SP - 256) RTT_K (rtt_writes 0) NoG L2 A2 mem2 md2 Lam2
      (SP - 256) t Db HG HC2 HNb).
    + intros bk Hb. exact Hb.
    + intros bk Hb. apply (Permutation_in _ (Permutation_sym HPm)).
      apply (gi_sub _ _ _ _ _ _ _ _ _ _ _ HG). exact Hb.
    + lia.
    + lia.
    + intros z Hzz. split; [unfold cwin; destruct crt_static as (_ & Herr & _); rewrite Herr;
        unfold strtod_c.STRTOD_ERRNO; unfold CRT_K in HK; lia|].
      intros [(X & _)|X]; [apply X; reflexivity | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X; lia].
    + intros z k Hak. split; [intros Hf; exact Hf|]. intros i Hi [(X & _)|X]; [apply X; reflexivity|].
      exact (proj1 (gi_blk_stat _ _ _ _ _ _ _ _ _ _ z k i HG Hak Hi) X).
  - rewrite <- G8. transitivity (getr regs1 8); [apply (HR 8); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - exact G10'.
  - split; [rewrite <- G2; transitivity (getr regs1 2); [apply (HR 2); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G3; transitivity (getr regs1 3); [apply (HR 3); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G4; transitivity (getr regs1 4); [apply (HR 4); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [rewrite <- G26; transitivity (getr regs1 26); [apply (HR 26); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    rewrite <- G27; transitivity (getr regs1 27); [apply (HR 27); unfold callee_saved; lia | rewrite Hg; reflexivity].
  - rewrite Hcnt. unfold cnt_r2. reflexivity.
  - exact HDf.
  - exact HDbl.
Qed.

Lemma crt_rw_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

(* A stack byte (no segment above the image) is writable exactly when it is present. *)
Lemma crt_wr_of_mbyte : forall m m' a, alloc_ceiling <= a < 2 ^ 64 ->
  mbyte segs m' a = mbyte segs m a -> writable_at segs m a -> writable_at segs m' a.
Proof.
  intros m m' a Ha E W.
  pose proof (crt_noseg_hi B (crt_img_low B HSEG) a Ha) as N.
  destruct (crt_img_low B HSEG) as [_ HI].
  unfold segs in *. pose proof alloc_ceiling_value.
  assert (Fs : find_segment (ms_segs B) a 1 = None).
  { destruct (find_segment (ms_segs B) a 1) as [g|] eqn:Fg; [|reflexivity]. destruct (HI a g Fg). lia. }
  unfold writable_at, wview in *. unfold mbyte in E. rewrite N in E.
  rewrite MState.unsigned_lit in W |- * by lia. rewrite Fs in W |- *.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [discriminate|].
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate | exact W].
Qed.

(* 0x14038: round_trip_text (doc, 0, &copy) returned 1 (memory had run out): s1 = 1, pj_free (&copy) of the copy
   that is still empty, return 1 *)
Lemma st1o : forall fx L A regs mem md Lam peak,
  gi fx L A mem md Lam peak (cnt0 + wcalls t false) (rtt_bo F b0 cnt0 t false) [] ->
  pj_zero segs mem (SP - 256) -> (ro <> 0 \/ oo <> 0) ->
  getr regs 10 = Z_to_bv 64 1 -> rbase regs ->
  SR segs (mkCfg (@mkst fx regs (Z_to_bv 64 0x14038) mem (seg_rom segs)) md) cpost.
Proof.
  intros fx L A regs mem md Lam peak HG HZr Hro' G10 (G2 & G3 & G4 & G26 & G27).
  pose proof HG as (HC & _). pose proof HC as (HM & _).
  destruct (kb_md B API L A mem md HM) as (Hh & Hz).
  apply (kb_run (fx := fx) B regs _ mem md
    (fun R pc' mem' => R = mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
        (getr regs 6) (getr regs 7) (getr regs 8) (Z_to_bv 64 1) (Z_to_bv 64 1) (getr regs 11) (getr regs 12)
        (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
        (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
        (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
      pc' = Z_to_bv 64 0x14248 /\ mem' = mem) _ Hh Hz).
  { unfold rmk. rewrite G10. unfold segs. rewrite HSEG.
    eapply Exec.evt_mono.
    - apply (crt_r1o (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
        (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
        (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem).
    - intros ms0 E. cbv beta in E. rewrite E. do 3 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; reflexivity. }
  intros R pc' mem' regs' (-> & -> & ->) Hg.
  apply (st8 fx L A regs' mem md Lam peak (cnt0 + wcalls t false) (rtt_bo F b0 cnt0 t false) JNull [] 0 1 HG).
  - exact (pj_zero_node segs mem (lin Lam) (SP - 256) HZr).
  - cbn [depth]. lia.
  - split; [rewrite Hg; exact G2|]. split; [rewrite Hg; exact G3|]. split; [rewrite Hg; exact G4|].
    split; [rewrite Hg; exact G26 | rewrite Hg; exact G27].
  - rewrite Hg. reflexivity.
  - intros Dc' HPc. apply Permutation_nil in HPc. subst Dc'.
    left. split; [reflexivity|]. split; [exact Hro'|]. split; reflexivity.
Qed.

Lemma st0 : SR segs (mkCfg (@mkst fx0 regs0 (Z_to_bv 64 CHECK_ROUND_TRIP) mem0 (seg_rom segs)) md0) cpost.
Proof.
  destruct crt_sp as (Hsp1 & Hsp16 & _ & Hsp2). pose proof alloc_ceiling_value as Hc.
  pose proof crt_doc as (Hd1 & Hd2).
  pose proof crt_m_le as Hm0.
  pose proof crt_tdep as (Hdt & _).
  destruct crt_env as (Hce & H47 & _ & G2 & Hra0 & _ & _).
  pose proof HRE as (_ & _ & _ & _ & _ & HP0 & _ & _ & Hfz0 & (Hro0 & _)).
  pose proof HP0 as (HM0 & HW0' & HB0' & _ & _ & _ & _ & Hstk & _ & Herr & _).
  destruct (kb_md B API L0 A0 mem0 md0 HM0) as (Hh & Hz).
  pose proof (kb_stk B API (crt_img_low B HSEG) _ L0 A0 _ mem0 md0 HP0 ltac:(unfold CRT_K; lia)) as Hst0.
  fold SP in Hst0. unfold segs in Hst0. rewrite HSEG in Hst0.
  assert (Hro0' : ro_agree rsegs mem0) by (unfold segs in Hro0; rewrite HSEG in Hro0; exact Hro0).
  assert (Hs0 : bv_unsigned (getr regs0 2) = SP) by (rewrite G2; apply crt_uns; lia).
  eapply (crt_kAn fx0 regs0 _ mem0 md0 _ cpost Hh Hz Hro0').
  { unfold rmk.
    apply (crt_pro HMS (getr regs0 1) (getr regs0 2) (getr regs0 3) (getr regs0 4) (getr regs0 5) (getr regs0 6)
      (getr regs0 7) (getr regs0 8) (getr regs0 9) (getr regs0 10) (getr regs0 11) (getr regs0 12) (getr regs0 13)
      (getr regs0 14) (getr regs0 15) (getr regs0 16) (getr regs0 17) (getr regs0 18) (getr regs0 19)
      (getr regs0 20) (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (getr regs0 25)
      (getr regs0 26) (getr regs0 27) (getr regs0 28) (getr regs0 29) (getr regs0 30) (getr regs0 31)
      fp_regs fp_csr (normalize rsegs mem0) (SP - CRT_K)); rewrite ?Hs0.
    - apply crt_stk_norm; [exact Hst0 | unfold CRT_K in *; lia | lia].
    - unfold CRT_F, CRT_K; lia.
    - exact (mem_inv_normalize rsegs mem0). }
  { intros ms0 (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & _).
    eexists _, _, _. exact E. }
  intros R pc' mem' m0 regs1 HQ HRl Hsame Hg.
  destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & E & MU & WM & _ & HCL & HCP).
  crt_inj E R pc' m0.
  rewrite Hs0 in MU, HCL, HCP.
  pose proof (mem_rel_normalize rsegs mem0 Hro0') as HR0.
  pose proof (munch_rel rsegs _ mem0 _ mem' m1 HR0 HRl Hsame MU) as MU'.
  pose proof (wmono_rel rsegs mem0 _ mem' m1 HR0 HRl Hsame WM) as WM'.
  pose proof (ro_agree_same rsegs mem0 mem' Hro0' Hsame) as Hro'.
  pose proof (crt_rw_rel mem' m1 _ _ HRl HCL) as HCL'.
  pose proof (crt_rw_rel mem' m1 _ _ HRl HCP) as HCP'.
  rewrite <- HSEG in WM', Hro', HCL', HCP'.
  assert (HO : forall z, 0 <= z < alloc_ceiling ->
      Frame.outside [(SP + -88, SP); (SP + -256, SP + -200)] z)
    by (intros z Hzz; cbn [Frame.outside]; unfold CRT_K in *; split; [lia | split; [lia | exact I]]).
  assert (HG0 : gi fx0 L0 A0 mem' md0 Lam0 peak0 cnt0 b0 []).
  { split.
    { apply (cstep_munch B API SP CRT_K alloc_statics NoG L0 A0 mem0 md0 L0 A0 mem0 md0 mem'
        [(SP + -88, SP); (SP + -256, SP + -200)] (crt_img_low B HSEG));
        [unfold CRT_K in *; lia | | exact MU' | exact WM' |].
      - apply (cstep_refl B API); [exact HM0 | exact HW0' | exact HB0' |].
        intros a [Ha|Ha]; [apply Hstk; fold SP; exact Ha | apply Herr; exact Ha].
      - intros z Hzz Hn. cbn [Frame.outside]. unfold CRT_K in *. split; [lia | split; [lia | exact I]]. }
    split; [exact Hro'|].
    split; [exact HI0|]. split; [exact Hfz0|]. split; [intros r Hr; reflexivity|].
    split; [exact (ledger_munch B API L0 A0 mem0 md0 mem' Lam0 peak0 cnt0 _ _ HM0 HL0 MU' HO)|].
    split; [lia|]. split; [apply Permutation_refl|]. split; [intros a k []|]. split; [exact HB0|].
    split; [unfold cells0; replace (SP - 88) with (SP + -88) by lia; exact HCL'|].
    apply (pj_node_munch segs _ mem0 (lin Lam0) mem' (lin Lam0) doc t D HN0 (fun a k H => HD0 _ H) MU').
    intros z [Hzz|([ba bk] & Hb & Hzz)]; [cbn [Frame.outside]; split; [lia | split; [lia | exact I]]|].
    destruct (ledger_block_range B API L0 A0 mem0 md0 Lam0 peak0 cnt0 _ ba bk HM0 HL0 (HD0 _ Hb)) as (X1 & X2 & _).
    unfold pj_holds in Hzz. cbn [fst snd] in Hzz. apply HO. lia. }
  pose proof HG0 as (HC & Hro & Hin & Hfz & Hfk & HL & Hpk & HP & HNB & Hres & Hcells & HN).
  pose proof HC as (HM & _).
  assert (H2 : getr regs1 2 = Z_to_bv 64 (SP - 256)) by (rewrite Hg; f_equal; lia).
  assert (H4 : getr regs1 4 = getr regs0 4) by (rewrite Hg; reflexivity).
  assert (H1 : getr regs1 1 = Z_to_bv 64 0x14038) by (rewrite Hg; reflexivity).
  assert (Hra : YK0s.ret_ok (getr regs1 1)) by (rewrite H1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
  assert (Hs : spZ regs1 = SP - 256) by (unfold spZ; rewrite H2; apply crt_uns; lia).
  assert (HK : 0 <= RTT_K <= CRT_K - 256) by (unfold CRT_K; split; apply Z.leb_le; vm_compute; reflexivity).
  assert (Hwl : wlen t false + 1 <= 2 ^ 28) by lia.
  assert (Hcopy0 : Mem.bytes_at segs mem' (SP - 256) (repeat (Z_to_bv 8 0) 56)).
  { destruct HCP' as [[_ HB] _]. replace (SP - 256) with (SP + -256) by lia. exact HB. }
  change (Z_to_bv 64 0x14d88) with (Z_to_bv 64 ROUND_TRIP_TEXT).
  eapply SR_bind.
  { apply (HRTT fx0 L0 A0 regs1 mem' md0 Lam0 peak0 cnt0 b0 doc 0 (SP - 256) t D ro oo).
    - exact (crt_renv fx0 L0 A0 mem' md0 Lam0 peak0 cnt0 b0 _ regs1 _ HG0 H2 H4 Hra HK).
    - exact Hin.
    - exact HL.
    - lia.
    - exact Hres.
    - rewrite Hg. exact HA0.
    - rewrite Hg. reflexivity.
    - rewrite Hg; f_equal; lia.
    - left. reflexivity.
    - exact HN.
    - exact HD0.
    - lia.
    - lia.
    - eapply PjRoundTrip.wf_read. exact HX.
    - exact Hdt.
    - exact Hwl.
    - right. split; [lia|]. split; [split; [Z.div_mod_to_equations; lia|]|].
      + apply (gi_stk_in _ _ _ _ _ _ _ _ _ _ _ _ HG0); unfold CRT_K; lia.
      + split; [lia | left; lia].
    - change (negb (0 =? 0)) with false. exact HRM1.
    - exact HRO.
    - exact HOO.
    - exact (proj1 (gi_flags _ _ _ _ _ _ _ _ _ _ HG0)).
    - exact (proj2 (gi_flags _ _ _ _ _ _ _ _ _ _ HG0)). }
  intros c' (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & -> & FZ2 & FK2 & RR2 & RD2 & _ & _ & Harms).
  try change (negb (0 =? 0)) with false in *.
  destruct (rtt_cstep B API _ regs1 _ L0 A0 mem' md0 L2 A2 regs2 mem2 md2 RR2) as [HC2 HR].
  pose proof RR2 as (_ & _ & _ & Hin' & _).
  rewrite Hs in HC2.
  assert (Hrb : rbase regs2).
  { split; [transitivity (getr regs1 2); [apply (HR 2); unfold callee_saved; lia | exact H2]|].
    split; [transitivity (getr regs1 3); [apply (HR 3); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    split; [transitivity (getr regs1 4); [apply (HR 4); unfold callee_saved; lia | exact H4]|].
    split; [transitivity (getr regs1 26); [apply (HR 26); unfold callee_saved; lia | rewrite Hg; reflexivity]|].
    transitivity (getr regs1 27); [apply (HR 27); unfold callee_saved; lia | rewrite Hg; reflexivity]. }
  destruct Harms as [(Hro2 & G10' & LG2 & Hpk2 & HN2 & HPm & Hres' & Hcp) | (Z1 & Z2 & G10' & LG2 & Hpk2 & HN2 & _ & Hc1)].
  - (* memory had run out *)
    assert (Hcp' : forall a, SP - 256 <= a < SP - 256 + 56 -> mbyte segs mem2 a = mbyte segs mem' a).
    { intros a Ha. replace a with (SP - 256 + (a - (SP - 256))) by lia. apply Hcp; lia. }
    assert (HG' : gi fx2 L2 A2 mem2 md2 Lam2 peak2 (cnt0 + wcalls t false) (rtt_bo F b0 cnt0 t false) []).
    { apply (gi_step fx0 fx2 L0 A0 mem' md0 Lam0 peak0 cnt0 b0 [] (SP - 256) RTT_K (rtt_writes (SP - 256)) NoG
               L2 A2 mem2 md2 Lam2 peak2 _ _ [] HG0 HC2).
      - unfold CRT_K in *. lia.
      - lia.
      - intros a [(_ & X)|X]; [left; lia | right; left; exact X].
      - intros a k _ Hf. exact Hf.
      - intros a Ha. unfold rtt_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
      - intros a Ha [(_ & X)|X].
        + apply (crt_wr_of_mbyte mem' mem2 a ltac:(unfold CRT_K in *; lia) (Hcp' a X)).
          destruct (gi_stk_in _ _ _ _ _ _ _ _ _ _ (SP - 256) (SP - 200) HG0 ltac:(unfold CRT_K; lia)
            ltac:(lia) ltac:(lia)) as (_ & _ & Hw).
          destruct (Hw a ltac:(lia)) as [Hw' _]. unfold writable_at. exact Hw'.
        + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
      - exact (proj1 RD2).
      - apply Hin'. exact Hin.
      - exact FZ2.
      - intros r Hr. exact (FK2 r Hr).
      - exact LG2.
      - exact Hpk2.
      - exact HPm.
      - intros a k [].
      - exact Hres'. }
    rewrite H1.
    apply (st1o fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 HG').
    + split; [split; [Z.div_mod_to_equations; lia|]|].
      * apply (gi_stk_in _ _ _ _ _ _ _ _ _ _ _ _ HG'); unfold CRT_K; lia.
      * apply (crt_bytes_frame segs mem' mem2 _ _ Hcopy0). rewrite repeat_length. intros i Hi.
        apply Hcp'. cbn in Hi. lia.
    + exact Hro2.
    + exact G10'.
    + exact Hrb.
  - destruct (Hc1 ltac:(lia)) as (Hres' & Db & HPm & HNB2 & HNb & HLz & HNl).
    assert (HG' : gi fx2 L2 A2 mem2 md2 Lam2 peak2 (cnt0 + wcalls t false + Z.of_nat (PjRoundTrip.tcalls t))
        (crt_b1 F b0 cnt0 t) Db).
    { apply (gi_step fx0 fx2 L0 A0 mem' md0 Lam0 peak0 cnt0 b0 _ (SP - 256) RTT_K (rtt_writes (SP - 256)) NoG
               L2 A2 mem2 md2 Lam2 peak2 _ (crt_b1 F b0 cnt0 t) _ HG0 HC2).
      - unfold CRT_K in *. lia.
      - lia.
      - intros a [(_ & X)|X]; [left; lia | right; left; exact X].
      - intros a k _ Hf. exact Hf.
      - intros a Ha. unfold rtt_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
      - intros a Ha [(_ & X)|X]; [exact (crt_node_wr _ _ _ _ _ HNb a X)|].
        unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in X. lia.
      - exact (proj1 RD2).
      - apply Hin'. exact Hin.
      - exact FZ2.
      - intros r Hr. exact (FK2 r Hr).
      - exact LG2.
      - exact Hpk2.
      - exact HPm.
      - exact HNB2.
      - exact Hres'. }
    rewrite H1.
    apply (st1 fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 _ Db (conj Z1 Z2) HG' HNb).
    + transitivity (getr regs1 8); [apply (HR 8); unfold callee_saved; lia | rewrite Hg; exact HA0].
    + exact G10'.
    + exact Hrb.
    + unfold cnt_r1. reflexivity.
    + exact (conj HLz HNl).
Qed.

End Calls.

End Main.

Section T.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGF : globals_free B API GIInit.omx_G.
Hypothesis HRTT : forall fx, @round_trip_text_contract fx rc B API F.
Hypothesis HPS : forall fx, @pj_string_contract fx rc B API F.
Hypothesis HSET : forall fx, @pj_set_contract fx rc B API F.
Variable kw : jv -> Z.
Hypothesis HKW : forall u, (depth u <= 32)%nat -> 0 <= kw u <= PJ_PARSE_K.
Hypothesis HW : forall fx, @pj_write_hyp fx rc B API F kw.
Hypothesis HPN : forall fx, @parse_noting_contract fx rc B API F.
Hypothesis HFF : forall fx, @fuzz_free_contract fx rc B API F.
Hypothesis HPF : forall fx, @pj_free_contract fx rc B API F.
Hypothesis HSL : strlen_contract.
Hypothesis HSC : strcmp_contract.
Hypothesis HSM : same_contract.
Hypothesis HMS : memset_contract.
Hypothesis HROc : fuzz_alloc_ran_out_contract.

Theorem check_round_trip_holds : forall fx, @check_round_trip_contract fx rc B API F.
Proof.
  intros fx. unfold check_round_trip_contract.
  intros L A regs mem md Lam peak cnt b doc t D x ro oo HRE HI HL HC HB HA HN HD HSD HX HXL HW0 HW1 HRM1 HRM2 HOBJ HTR
    Hro Hoo HFR HFO.
  pose proof HRE as (HSEG & _).
  eapply (st0 B API F AX HSEG L A regs mem md Lam peak cnt b doc t D x); eassumption.
Qed.

End T.
