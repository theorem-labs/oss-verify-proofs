(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeam02x.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* The conversion %02x (Px02) at the seam, on the per-piece arms (FMgxaSeamPf.v :98-111): the text arm,
   the model-arguments arm (the ARGS facts: a %02x argument is an AInt v, and GXA's model takes PA_u (v mod 2^32), which
   pt_parg_ok allows), and the bytes arm; then a NON-VACUITY control at fuzz_disco's own format.
   New file beside FMgxaSeamPf.v; nothing in it is edited.
   - the text arm needs the one equation PT.pf_hex2 = pf_hex2 (an induction over the digit fuel, pt_pf_hexs; the same
     two lemmas as fuzz_disco's lib/A/FMgxaSeamPf.v);
   - the bytes arm: every digit pf_hexd d of pf_hexs is a byte, and so are the zeros pf_hex2 pads with;
   - the control: fuzz_disco.c:592's "%02x:%02x:%02x:%02x:%02x:%02x" (29 bytes at .rodata 0x20f80 in both images, read
     from the pinned image of libreac/fuzz_disco's ASan build, sha256 5e39150dd8104df9...), with six concrete AInt
     arguments: it parses to six Px02 and five ':' pieces, each piece has its three arms, and GXA's model reads the
     six arguments as PA_u of each. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMpfStep FMgxaSeamPf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the one equation ---- *)
Lemma pt_pf_hexs_02x : forall fuel x acc, PT.pf_hexs fuel x acc = pf_hexs fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_hexs pf_hexs]. destruct (x <? 16); [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma pt_pf_hex2_02x : forall v, PT.pf_hex2 v = pf_hex2 v.
Proof. intros v. unfold PT.pf_hex2, pf_hex2. cbv zeta. rewrite pt_pf_hexs_02x. reflexivity. Qed.

(* ---- the three arms at Px02 ---- *)
Lemma seam_text_arm_px02 : seam_text_arm Px02.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text]. rewrite pt_pf_hex2_02x.
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_px02 : seam_pargs_arm Px02.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [AInt v], [PA_u (v mod 2^32)].
split; [reflexivity|].
split; [constructor; [right; exists v; split; reflexivity | constructor] | reflexivity].
Qed.

Lemma pf_hexd_byte : forall d, 0 <= d < 16 -> 0 <= pf_hexd d < 256.
Proof. intros d Hd. unfold pf_hexd. destruct (d <? 10); lia. Qed.

Lemma pf_hexs_bytes : forall fuel x acc, 0 <= x -> Forall (fun b => 0 <= b < 256) acc ->
  Forall (fun b => 0 <= b < 256) (pf_hexs fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; [exact Hacc|].
cbn [pf_hexs]. destruct (x <? 16) eqn:E.
- apply Z.ltb_lt in E. constructor; [apply pf_hexd_byte; lia | exact Hacc].
- apply Z.ltb_ge in E. apply IH; [apply Z.div_pos; lia|].
  constructor; [apply pf_hexd_byte; apply Z.mod_pos_bound; lia | exact Hacc].
Qed.

Lemma seam_bytes_arm_px02 : seam_bytes_arm Px02.
Proof.
intros args c a' _ _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. unfold pf_hex2. cbv zeta. apply Forall_app. split.
- apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
- apply pf_hexs_bytes; [apply Z.mod_pos_bound; lia | constructor].
Qed.

(* ---- NON-VACUITY control: fuzz_disco's "%02x:%02x:%02x:%02x:%02x:%02x" ---- *)
Definition disco_mac_fmt02 : list Z :=
  [37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
   37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120].
Definition disco_mac_ps02 : list pf_piece :=
  [Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02].
Definition disco_mac_vals02 : list Z := [0xde; 0xad; 0xbe; 0xef; 0x00; 0x01].
Definition disco_mac_args02 : list pf_arg := map AInt disco_mac_vals02.

Lemma disco_mac02_parse : pf_parse disco_mac_fmt02 = Some disco_mac_ps02.
Proof. vm_compute. reflexivity. Qed.

(* the pieces are exactly ':' literals and %02x, so the three arms above (and FMgxaSeamPf.v's lit arms) cover them *)
Definition pk_02x (p : pf_piece) : Prop := match p with PLit _ | Px02 => True | _ => False end.
Lemma disco_mac02_pk : Forall pk_02x disco_mac_ps02.
Proof. repeat constructor. Qed.
Lemma pk_02x_text : forall p, pk_02x p -> seam_text_arm p.
Proof. intros p Hp. destruct p; try (exfalso; exact Hp); [apply seam_text_arm_lit | exact seam_text_arm_px02]. Qed.
Lemma pk_02x_pargs : forall p, pk_02x p -> seam_pargs_arm p.
Proof. intros p Hp. destruct p; try (exfalso; exact Hp); [apply seam_pargs_arm_lit | exact seam_pargs_arm_px02]. Qed.
Lemma pk_02x_bytes : forall p, pk_02x p -> seam_bytes_arm p.
Proof. intros p Hp. destruct p; try (exfalso; exact Hp); [apply seam_bytes_arm_lit | exact seam_bytes_arm_px02]. Qed.

(* renders the MAC "de:ad:be:ef:00:01", in both renderers *)
Definition disco_mac02_text : list Z := [100; 101; 58; 97; 100; 58; 98; 101; 58; 101; 102; 58; 48; 48; 58; 48; 49].
Lemma disco_mac02_render : pf_text disco_mac_ps02 disco_mac_args02 = Some disco_mac02_text.
Proof. vm_compute. reflexivity. Qed.
Lemma disco_mac02_render_model :
  PT.pf_text (map pt_piece disco_mac_ps02) (map pt_arg disco_mac_args02) = Some disco_mac02_text.
Proof. vm_compute. reflexivity. Qed.

(* the ARGS facts at work: GXA's model reads the six arguments as PA_u of each, and each is pt_parg_ok *)
Lemma disco_mac02_pargs :
  PT.pf_pargs (map pt_piece disco_mac_ps02) (map pt_arg disco_mac_args02) = map (fun v => PA_u (v mod 2^32)) disco_mac_vals02
  /\ Forall2 pt_parg_ok disco_mac_args02 (map (fun v => PA_u (v mod 2^32)) disco_mac_vals02).
Proof.
split; [vm_compute; reflexivity|].
cbn [disco_mac_args02 disco_mac_vals02 map].
repeat (apply Forall2_cons; [right; eexists; split; reflexivity|]). apply Forall2_nil.
Qed.

(* and the argument list is not fm's form: pt_parg would give PA_i, the model PA_u *)
Lemma disco_mac02_not_pt_parg : map pt_parg disco_mac_args02 <> map (fun v => PA_u (v mod 2^32)) disco_mac_vals02.
Proof. vm_compute. discriminate. Qed.
