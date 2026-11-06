(* ASan's printf_common scan (lib/A/Bz/A/I_pcxgram.v pcx_walk / pcx_covs, the grammar the released Bz walk
   lib/A/Bz/A/I_pcxlist.v pcom_genx_spec takes) accepts every segconf format (lib/A/Rt/RtPFSeg.v seg_parse) with its
   arguments, and gives each argument the coverage entry seg_cinK: RT_pf_sh.v's grammar part (pcom_pcx_arm, pcx_K,
   pcomx_K) over seg_piece.
   - the per-piece arm seg_pcx_arm q: one pcx_walk step reads q's code with the arguments q consumes;
   - the three new pieces have their arm here, each one pcx_dir step: %u is PK_int (I_pcxgram.v pcx_conv 'u'),
     %zu is the length flag 'z' then 'u', PK_long (pcx_lmp), %.24s is a numeric precision (pcx_precp PP_num) on PK_str;
     each consumes one argument with coverage None (the walk range-checks a %.24s string as a whole C string);
   - Section PcomS: for any piece predicate whose pieces have their arm, the scan accepts the format.
   The released pieces' arms (RT_pf_d.v, RT_pf_c.v, ...) are carried to PRel p in SegPcomU.v. Pure: no machine
   state, no image value. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegPfStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* a pf argument as the Bz grammar's argument kind (RT_pf_sh.v pa_of, the same body) *)
Definition seg_pa_of (a : pf_arg) : parg :=
  match a with AInt v => PA_i v | AU64 u => PA_u u | APtr s => PA_s s end.

(* the coverage entries of the arguments one piece consumes (RT_pf_sh.v pc_cin1 at PRel p; one None for each new
   piece) *)
Definition seg_cin1 (q : seg_piece) : list (option Z) :=
  match q with PRel (PLit _) => [] | PRel Pps => [None; Some 0] | _ => [None] end.
Fixpoint seg_cinK (qs : list seg_piece) : list (option Z) :=
  match qs with [] => [] | q :: qs' => seg_cin1 q ++ seg_cinK qs' end.

(* the pcx arm (RT_pf_sh.v pcom_pcx_arm over seg_piece) *)
Definition seg_pcx_arm (q : seg_piece) : Prop :=
  forall (fuel : nat) (rest : list Z) (args : list pf_arg) (c : list Z) (a' : list pf_arg) (C : list (option Z)),
    seg_code_ok q -> seg_step q args = Some (c, a') ->
    (forall n, pcx_walk fuel rest (map seg_pa_of a') = Some n ->
       exists n', pcx_walk (S fuel) (seg_code q ++ rest) (map seg_pa_of args) = Some n') /\
    pcx_covs (S fuel) (seg_code q ++ rest) (map seg_pa_of args) (seg_cin1 q ++ C) =
      seg_cin1 q ++ pcx_covs fuel rest (map seg_pa_of a') C.

(* ---- the three new pieces have their arm ---- *)
Lemma seg_pcx_arm_u : seg_pcx_arm Pu.
Proof.
intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
injection H as <- <-. split.
- intros n W. exists (1 + n)%nat. cbn [seg_code app map seg_pa_of pcx_walk]. cbn. rewrite W. reflexivity.
- cbn [seg_code seg_cin1 app map]. cbn. reflexivity.
Qed.
Lemma seg_pcx_arm_zu : seg_pcx_arm Pzu.
Proof.
intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
injection H as <- <-. split.
- intros n W. exists (1 + n)%nat. cbn [seg_code app map seg_pa_of pcx_walk]. cbn. rewrite W. reflexivity.
- cbn [seg_code seg_cin1 app map]. cbn. reflexivity.
Qed.
Lemma seg_pcx_arm_24s : seg_pcx_arm P24s.
Proof.
intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [seg_step] in H; try discriminate H.
injection H as <- <-. split.
- intros n W. exists (1 + n)%nat. cbn [seg_code app map seg_pa_of pcx_walk]. cbn. rewrite W. reflexivity.
- cbn [seg_code seg_cin1 app map]. cbn. reflexivity.
Qed.

(* ==== printf_common's grammar for any piece predicate PK whose pieces have their pcx arm ==== *)
Section PcomS.
Variable PK : seg_piece -> Prop.
Hypothesis ARM_pcx : forall q, PK q -> seg_pcx_arm q.

Lemma seg_pcx_K : forall fuel fmt qs args T,
  (length fmt < fuel)%nat -> seg_parse fmt = Some qs -> Forall PK qs -> seg_text qs args = Some T ->
  (exists n, pcx_walk fuel (fmt ++ [0]) (map seg_pa_of args) = Some n) /\
  pcx_covs fuel (fmt ++ [0]) (map seg_pa_of args) (seg_cinK qs) = seg_cinK qs.
Proof.
  induction fuel as [|fuel IH]; intros fmt qs args T Hf Hp HK HT; [lia|].
  destruct qs as [|q qs].
  - rewrite (seg_parse_nil fmt Hp). cbn in HT. destruct args as [|a args]; [|discriminate HT].
    split; [exists 0%nat; reflexivity | reflexivity].
  - destruct (seg_parse_split fmt q qs Hp) as (r & -> & Hr & Hok).
    inversion HK as [|? ? Hk HK1]; subst.
    rewrite seg_text_step in HT. destruct (seg_step q args) as [[c a']|] eqn:ES; [|discriminate HT].
    destruct (seg_text qs a') as [T1|] eqn:HT1; [|discriminate HT].
    pose proof (seg_code_len q) as L.
    rewrite length_app in Hf.
    destruct (IH r qs a' T1 ltac:(lia) Hr HK1 HT1) as ((n1 & W1) & C1).
    destruct (ARM_pcx q Hk fuel (r ++ [0]) args c a' (seg_cinK qs) Hok ES) as (AW & AC).
    rewrite <- app_assoc. split.
    + exact (AW n1 W1).
    + change (seg_cinK (q :: qs)) with (seg_cin1 q ++ seg_cinK qs). rewrite AC, C1. reflexivity.
Qed.

Lemma seg_pcomx_K : forall fmt qs args T,
  seg_parse fmt = Some qs -> Forall PK qs -> seg_text qs args = Some T ->
  pcomx_ok (fmt ++ [0]) (map seg_pa_of args) = true /\
  pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map seg_pa_of args) (seg_cinK qs) = seg_cinK qs.
Proof.
  intros fmt qs args T Hp HK HT.
  destruct (seg_pcx_K (length (fmt ++ [0])) fmt qs args T ltac:(rewrite length_app; cbn; lia) Hp HK HT)
    as ((n & W) & C).
  split; [unfold pcomx_ok; rewrite W; reflexivity | exact C].
Qed.
End PcomS.

(* ---- controls: the three new conversions on printf_common's grammar, by computation ---- *)
Example seg_pcx_control :
  pcomx_ok [37; 117; 0] (map seg_pa_of [AInt (-1)]) = true /\
  pcomx_ok [37; 122; 117; 0] (map seg_pa_of [AU64 46]) = true /\
  pcomx_ok [37; 46; 50; 52; 115; 0] (map seg_pa_of [APtr [97; 98]]) = true /\
  pcx_covs 6 [37; 46; 50; 52; 115; 0] (map seg_pa_of [APtr [97; 98]]) [None] = [None].
Proof. repeat split; vm_compute; reflexivity. Qed.
