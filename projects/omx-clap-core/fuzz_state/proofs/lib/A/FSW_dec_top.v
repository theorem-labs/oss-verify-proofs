(* preset_base64_decode: the composition of the three stages and the two spec bridges (scratch part T, owner a Theorem Labs lane) *)
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
FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_dec_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* fpostU is monotone in its Q *)
Lemma decT_fpostU_mono : forall STK sp0 FP regs ly S U W mem md k U'
  (Q Q' : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  (forall ly' S' W2 regs' mem' md', Q ly' S' W2 regs' mem' md' -> Q' ly' S' W2 regs' mem' md') ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k U' Q W' c' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k U' Q' W' c'.
Proof.
intros STK sp0 FP regs ly S U W mem md k U' Q Q' W' c' HQ (ly' & S' & regs' & mem' & md' & Ec & HJ & OK & PO & HP & Hq).
exists ly', S', regs', mem', md'. repeat (split; [eassumption|]). apply HQ. exact Hq.
Qed.

(* the three stages compose into the whole function *)
Lemma dec_walk : dec_stage_entry B -> dec_stage_loop B -> dec_stage_free B ->
  forall d, dec_entry_ok B d ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d).
Proof.
intros HE HL HF d Hd. apply (HE d Hd).
intros Wc lyc Sc Uc regsc memc mdc k q Hh. apply (HL d q 0%nat [] 0 0 Wc lyc Sc Uc regsc memc mdc k Hd Hh).
intros W3 ly3 S3 U3 regs3 mem3 md3 k3 Hf. exact (HF d q W3 ly3 S3 U3 regs3 mem3 md3 k3 Hd Hf).
Qed.

(* decode_spec (the real-stack placement of *lenp): the walk's entry bundle from decode_spec's premises *)
Lemma dec_entry_ok_real : forall ly S U W regs mem md ch ot text lenp tb live peak cnt fail v,
  fpreU tfibsegs B STK_preset_base64_decode ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 text -> getr regs 11 = w64 lenp ->
  cstr_ok tfibsegs W mem text tb -> wsrc_kept B tfibsegs ly S U W mem 0 text (tb ++ [0]) ->
  WriterSpec.bytes_ok tb -> Z.of_nat (length tb) <= 2 ^ 28 ->
  lenp mod 8 = 0 -> spZ regs <= lenp -> lenp + 8 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) lenp 8 v -> 0 <= v < 2 ^ 64 ->
  (lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + dec_ev tb <= EV_MAX -> blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX ->
  live + dec_size tb < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  (exists chl, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) lenp chl) ->
  dec_entry_ok B (mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FS_PSTAT_FP).
Proof.
intros ly S U W regs mem md ch ot text lenp tb live peak cnt fail v HPRE HH HFR H10 H11 HCS HWS HBO HLEN
  Hl8 Hspl Hlot Hot16 Hottop HPRS HV Hv HDJ HG HEV HLV HLIVE HCNT HCH.
unfold dec_entry_ok; cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt
  d_fail d_v d_FP].
repeat match goal with |- _ /\ _ => split end;
first [ assumption | lia
      | left; repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity] ].
Qed.
(* the real-stack post is decode_spec's wpost *)
Lemma dec_post_real : forall ly S U W regs mem md ch ot text lenp tb live peak cnt fail v W' c',
  dec_post B (mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FS_PSTAT_FP) W' c' ->
  (cnt = fail /\
   wpost B tfibsegs STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md 0 U
     (fun ly' S' W' regs' mem' md' =>
        getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
        wkeep tfibsegs W W' mem mem' (spZ regs) ot lenp 8 /\
        val_mem tfibsegs (mrestrict (w_H W') mem') lenp 8 v /\
        fs_glob tfibsegs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
  \/
  (cnt <> fail /\ WriterSpec.b64_dec tb = None /\
   wpost B tfibsegs STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md EV_preset_base64_decode U
     (fun ly' S' W' regs' mem' md' =>
        getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
        wkeep tfibsegs W W' mem mem' (spZ regs) ot lenp 8 /\
        val_mem tfibsegs (mrestrict (w_H W') mem') lenp 8 v /\
        fs_glob tfibsegs W' mem' live (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail) W' c')
  \/
  (exists q out, cnt <> fail /\ WriterSpec.b64_dec tb = Some out /\ q <> 0 /\
   wpost B tfibsegs STK_preset_base64_decode ot FS_PSTAT_FP regs ly S U W mem md 1 (U ++ [(q - HEAD, HEAD)])
     (fun ly' S' W' regs' mem' md' =>
        getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
        ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)] /\
        fs_rblock tfibsegs B ly' S' W' mem' q (dec_size tb) /\
        zbytes_at tfibsegs W' mem' q out /\
        wkeep tfibsegs W W' mem mem' (spZ regs) ot lenp 8 /\
        val_mem tfibsegs (mrestrict (w_H W') mem') lenp 8 (Z.of_nat (length out)) /\
        cstr_ok tfibsegs W' mem' text tb /\
        fs_glob tfibsegs W' mem' (live + dec_size tb) (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail)
     W' c').
Proof.
intros ly S U W regs mem md ch ot text lenp tb live peak cnt fail v W' c' HP.
unfold dec_post, d_STKJ, d_sp in HP. cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak
  d_cnt d_fail d_v d_FP] in HP.
unfold wpost. exact HP.
Qed.

(* decode_spec_ff (the lenp slot in a live caller fake frame, top ot = sp, the slot in FP) from the walk's post *)
Lemma dec_decode_ff_of_post :
  (forall d, dec_entry_ok B d ->
     SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d)) ->
  decode_spec_ff B tfibsegs.
Proof.
intros H ly S U W regs mem md ch text lenp tb live peak cnt fail v HPRE HH HFR H10 H11 HCS HWS HBO HLEN
  Hl8 HFRM HPRS HRAL HV Hv HDJ HG HEV HLV HLIVE HCNT.
pose (d := mkDE ly S U W regs mem md ch (spZ regs) text lenp tb live peak cnt fail v (FS_PSTAT_FP ++ [(lenp, lenp + 8)])).
assert (Hd : dec_entry_ok B d).
{ unfold dec_entry_ok, d; cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt
    d_fail d_v d_FP].
  repeat match goal with |- _ /\ _ => split end;
  first [ assumption | lia
        | right; repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity] ]. }
eapply SRr_mono; [exact (H d Hd)|]. cbv beta. intros W' c' _ HP.
unfold dec_post, d, d_STKJ, d_sp in HP. cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak
  d_cnt d_fail d_v d_FP] in HP.
replace (STK_preset_base64_decode + (spZ regs - spZ regs)) with STK_preset_base64_decode in HP by lia.
destruct HP as [(Hc & HP) | [(Hc & Hb & HP) | (q & out & Hc & Hb & Hq & HP)]].
- left. split; [exact Hc|]. revert HP. apply decT_fpostU_mono.
  intros ly' S' W2 regs' mem' md' (A1 & A2 & _ & A4 & A5). tauto.
- right; left. split; [exact Hc|]. split; [exact Hb|]. revert HP. apply decT_fpostU_mono.
  intros ly' S' W2 regs' mem' md' (A1 & A2 & _ & A4 & A5). tauto.
- right; right. exists q, out. split; [exact Hc|]. split; [exact Hb|]. split; [exact Hq|]. revert HP.
  apply decT_fpostU_mono.
  intros ly' S' W2 regs' mem' md' (A1 & A2 & A3 & A4 & A5 & _ & A7 & A8 & A9). tauto.
Qed.

(* decode_spec (the real-stack placement of *lenp) from the walk's post *)
Lemma dec_decode_of_post :
  (forall d, dec_entry_ok B d ->
     SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d)) ->
  decode_spec B tfibsegs.
Proof.
intros H ly S U W regs mem md ch ot text lenp tb live peak cnt fail v HPRE HH HFR H10 H11 HCS HWS HBO HLEN
  Hl8 Hspl Hlot Hot16 Hottop HCH HPRS HV Hv HDJ HG HEV HLV HLIVE HCNT.
pose proof (dec_entry_ok_real ly S U W regs mem md ch ot text lenp tb live peak cnt fail v HPRE HH HFR H10 H11
  HCS HWS HBO HLEN Hl8 Hspl Hlot Hot16 Hottop HPRS HV Hv HDJ HG HEV HLV HLIVE HCNT HCH) as Hd.
eapply SRr_mono; [exact (H (mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FS_PSTAT_FP) Hd)|].
cbv beta. intros W' c' _ HP.
exact (dec_post_real ly S U W regs mem md ch ot text lenp tb live peak cnt fail v W' c' HP).
Qed.

(* the closing theorems from the three stages (each stage is proved under its own Section hypotheses; the final file
   instantiates these with them) *)
Theorem decode_of_stages : dec_stage_entry B -> dec_stage_loop B -> dec_stage_free B ->
  decode_spec B tfibsegs.
Proof. intros HE HL HF. apply dec_decode_of_post. exact (dec_walk HE HL HF). Qed.
Theorem decode_ff_of_stages : dec_stage_entry B -> dec_stage_loop B -> dec_stage_free B ->
  decode_spec_ff B tfibsegs.
Proof. intros HE HL HF. apply dec_decode_ff_of_post. exact (dec_walk HE HL HF). Qed.
End T.
