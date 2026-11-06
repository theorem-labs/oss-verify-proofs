#!/usr/bin/env python3
"""gen_y.py -- fuzz_disco asan-ubsan's position-abstract listing layer, in cgif_file_fuzzer's Y layout and names:
lib/Reusable/{YI0w,YI0z,YI12,YCef,YB1v,YC8i,YCbj}.v. Written from scratch from mklisting.py's output on
fuzz_disco.asan-ubsan, so no licence line and no comments.

usage: gen_y.py GEN DST RELRO_LO RELRO_HI NSEG MUSL_START TEXT_END GUARD_START
  GEN: the listing directory (listing.json, listing.body); DST: the directory the .v files are written to;
  RELRO_LO / RELRO_HI (hex): the read-only-after-relocation range, .data.rel.ro start .. .got end of the image's
  section headers; NSEG: the image's PT_LOAD count; MUSL_START (hex): the address of sysconf, the first function of
  the C library part of .text; TEXT_END (hex): the end of .text; GUARD_START (hex): the address of oft_exit_guard.
  The last three are used only in YB1v.v.
"""
import json
import os
import re
import sys

GEN, DST = sys.argv[1], sys.argv[2]
R = "OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable"
IMG = "OssFuzzTheorems.libreac.fuzz_disco.images"
RELRO_LO, RELRO_HI = int(sys.argv[3], 16), int(sys.argv[4], 16)
NSEG = int(sys.argv[5])
MUSL_START, TEXT_END, GUARD_START = int(sys.argv[6], 16), int(sys.argv[7], 16), int(sys.argv[8], 16)

m = json.load(open(os.path.join(GEN, "listing.json")))
body = open(os.path.join(GEN, "listing.body")).read().rstrip().rstrip(";")
NOBJ, NHI = len(m["objs"]), len(m["his"])


DONOR = {"__interceptor_trampoline_malloc": "malloc", "__interceptor_trampoline_free": "free"}


def raw_ident(n):
    return "".join(c if (c.isalnum() or c == "_") else "_" for c in n)


def ident(n):
    return DONOR.get(n, raw_ident(n))


def w(name, text):
    open(os.path.join(DST, name + ".v"), "w").write(text)


def yi0w():
    s = "From Stdlib Require Import ZArith.\nInductive asym : Type :=\n"
    s += "\n".join("| AS_%s" % ident(n) for n, _ in m["syms"]) + ".\n"
    w("YI0w", s)


def yi0z():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith List.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.\n"
         "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n"
         "From %s Require Import YP0b.\nFrom %s Require Import YI0w.\n"
         "Import ListNotations.\nOpen Scope bv_scope. Open Scope Z_scope.\n") % (R, R, R)
    for fn, off in sorted(m["funcs"].items(), key=lambda kv: kv[1]):
        s += "Definition AF_both3_%s : Z := 0x%x.\n" % (ident(fn), off)
    s += "Definition lib_both3_0_listing : ptable asym := [\n"
    b = body.replace("PCall DS_", "PCall AS_").replace("PTail DS_", "PTail AS_")
    for old, new in DONOR.items():
        b = re.sub(r"\bAS_%s\b" % re.escape(raw_ident(old)), "AS_" + new, b)
    s += b + "\n].\n"
    w("YI0z", s)


MUSL_COUNT = (TEXT_END - MUSL_START) // 4   # from sysconf to the end of .text
# GUARD_START: oft_exit_guard: auipc a0; lbu a0, (oft_in_callback); bnez a0, 8; ret
GUARD_COUNT = 4


def yb1v():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From %s Require Import YP02.\nFrom %s Require Import AsanUbsan.\n"
         "Unset Lia Cache. Unset Nia Cache.\n"
         "Open Scope Z_scope.\nDefinition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.\n"
         "Definition tfibmusl_text_start : Z := 0x%x.\n"
         "Definition tfibmusl_text_count : nat := %d.\n"
         "Definition tfibguard_start : Z := 0x%x.\n"
         "Definition tfibguard_count : nat := %d.\n"
         "Definition tfibmusl_tbl : ctable := Eval vm_compute in\n"
         "(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start "
         "tfibmusl_text_count TEmpty)).\n"
         "Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count "
         "(build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).\n"
         "Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.\n"
         "Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.\n"
         "Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. "
         "discriminate. Qed.\n") % (R, R, IMG, MUSL_START, MUSL_COUNT, GUARD_START, GUARD_COUNT)
    w("YB1v", s)


def ycef():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From %s Require Import YP02 YB1v.\nFrom %s Require Import AsanUbsan.\n"
         "Unset Lia Cache. Unset Nia Cache.\nOpen Scope Z_scope.\n"
         "Definition tfib_lib_start : Z := 0x%x.\n"
         "Definition tfib_lib_count : nat := %d.\n"
         "Definition tfibtbl_lib : ctable :=\n"
         "Eval vm_compute in (build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty).\n"
         "Lemma tfibtbl_lib_eq : tfibtbl_lib = build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty.\n"
         "Proof. vm_cast_no_check (eq_refl tfibtbl_lib). Qed.\n"
         "Lemma tfibtbl_lib_ok : table_ok tfibsegs tfibtbl_lib.\n"
         "Proof. rewrite tfibtbl_lib_eq. apply build_table_ok0. cbv. discriminate. Qed.\n") % (R, R, IMG, m["lo"],
                                                                                              m["nslots"])
    w("YCef", s)


def yi12():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith List Lia Bool.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n"
         "From %s Require Import YP0m YP02 YP0b YCef YB1v.\nFrom %s Require Import YI0w YI0z.\n"
         "From %s Require YImgTop.\n"
         "Import ListNotations.\nUnset Lia Cache. Unset Nia Cache.\nOpen Scope bv_scope. Open Scope Z_scope.\n"
         "Definition tfib_B0 : Z := 0x%x.\n") % (R, R, R, R, m["lo"])
    s += "Definition tfib_sigma (s : asym) : Z :=\nmatch s with\n"
    s += "".join("| AS_%s => 0x%x\n" % (ident(n), a) for n, a in m["syms"]) + "end.\n"
    s += "Definition tfib_nobj : nat := %d.\nDefinition tfib_obj (i : nat) : Z :=\nmatch i with\n" % NOBJ
    s += "".join("| %d%%nat => 0x%x\n" % (i, a) for i, a in enumerate(m["objs"])) + "| _ => 0\nend.\n"
    s += "Definition tfib_nhi : nat := %d.\nDefinition tfib_hi (j : nat) : Z :=\nmatch j with\n" % NHI
    s += "".join("| %d%%nat => 0x%x\n" % (j, a) for j, a in enumerate(m["his"])) + "| _ => 0\nend.\n"
    s += ("Definition tfib_val0 (a : nat) : Z :=\n"
          "if (a =? A_TEXT)%nat then tfib_B0 else if (a <? A_HI 0)%nat then tfib_obj (a - A_OBJ 0) "
          "else tfib_hi (a - A_HI 0).\n"
          "Lemma tfib_lib_check0 : pi_check asym (clookup tfibtbl_lib) tfib_val0 tfib_sigma lib_both3_0_listing = true.\n"
          "Proof. vm_compute. reflexivity. Qed.\n"
          "Lemma tfib_nobj_fits : (A_OBJ tfib_nobj <= A_HI 0)%nat.\nProof. vm_compute. lia. Qed.\n"
          "Lemma tfib_nhi_fits : (A_HI tfib_nhi <= 512)%nat.\nProof. vm_compute. lia. Qed.\n"
          "Lemma tfib_obj_img_chk : forallb (fun i => (YImgTop.IMG_LO <=? tfib_obj i) && (tfib_obj i + 8 <=? "
          "YImgTop.IMG_TOP)) (seq 0 tfib_nobj) = true.\nProof. vm_compute. reflexivity. Qed.\n"
          "Lemma tfib_segs_img_chk : forallb (fun s => (YImgTop.IMG_LO <=? Z.of_N (seg_base s)) && "
          "(Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? YImgTop.IMG_TOP)) tfibsegs = true.\n"
          "Proof. vm_compute. reflexivity. Qed.\n")
    w("YI12", s)


def yc8i():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List Lia Bool.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n"
         "From %s Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.\n"
         "From %s Require Import YM05.\n"
         "From %s Require Import YP0d YP0c YI0w YI0z YC4a.\n"
         "Import ListNotations.\nUnset Lia Cache. Unset Nia Cache.\n"
         "Local Set Warnings \"-abstract-large-number\".\nOpen Scope bv_scope.\nOpen Scope Z_scope.\n"
         "Definition both3_0_tpi : ptree asym := ptree_of_list lib_both3_0_listing.\n"
         "Definition both3_0_tw : ctable := Eval vm_compute in (tw_of 0 lib_both3_0_listing).\n"
         "#[global] Instance PL_both3_0 : PAListing lib_both3_0_listing :=\n"
         "{| pl_tpi := both3_0_tpi; pl_tpi_eq := eq_refl; pl_tw := both3_0_tw; "
         "pl_tw_eq := ltac:(vm_compute; reflexivity);\n"
         "pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); "
         "pl_slot0 := ltac:(vm_compute; exact I) |}.\n") % (R, R, R, R)
    w("YC8i", s)


def ycbj():
    zl = "Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.\n"
    pat = "[H|" * NSEG + "[]" + "]" * NSEG
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List Lia Bool.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n"
         "From %s Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a.\n"
         "From %s Require Import YK04 YG00 YG0f YG0n YG0d YM05.\n"
         "From %s Require Import YB1v YCef.\n"
         "From %s Require Import AsanUbsan.\n"
         "From %s Require Import YP0d YI0w YI0z YI12 YC4a YC8i YXcalls.\n"
         "From %s Require YImgTop.\n"
         "Import ListNotations.\nUnset Lia Cache. Unset Nia Cache.\n"
         "Local Set Warnings \"-abstract-large-number\".\nOpen Scope bv_scope.\nOpen Scope Z_scope.\n") % (
        R, R, R, R, IMG, R, R)
    s += zl
    s += ("Lemma tfib_val0_range : forall a, 0 <= tfib_val0 a < 2 ^ 64.\nProof.\n"
          "intros a. unfold tfib_val0. destruct (Nat.eqb a A_TEXT); [zlit|].\n"
          "destruct (Nat.ltb a (A_HI 0)).\n"
          "- unfold tfib_obj. generalize (a - A_OBJ 0)%%nat as m. intros m. do %d (destruct m as [|m]; [zlit|]). zlit.\n"
          "- unfold tfib_hi. generalize (a - A_HI 0)%%nat as m. intros m. do %d (destruct m as [|m]; [zlit|]). zlit.\n"
          "Qed.\n") % (NOBJ, NHI)
    s += ("Lemma tfib_wx : wx_segs_nowrap tfibsegs.\nProof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.\n")
    s += ("Lemma tfib_seg_in : forall a, in_img tfibsegs a -> exists b z, "
          "In (b, z) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) /\\ b <= a < b + z.\n"
          "Proof.\nintros a (sg & Hin & Hr). exists (Z.of_N (seg_base sg)), (Z.of_N (seg_size sg)). split; [|exact Hr].\n"
          "exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin).\nQed.\n")
    s += ("Lemma tfib_segs_low0 : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.\n"
          "Proof.\nintros a Ha. destruct (tfib_seg_in a Ha) as (b & z & H & Hr). unfold kLowMemEnd.\n"
          "vm_compute in H. destruct H as %s; injection H as <- <-; lia.\nQed.\n") % pat
    s += ("Lemma tfib_img_range0 : forall a, in_img tfibsegs a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.\n"
          "Proof.\nintros a Ha. destruct (tfib_seg_in a Ha) as (b & z & H & Hr). unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.\n"
          "vm_compute in H. destruct H as %s; injection H as <- <-; lia.\nQed.\n") % pat
    s += "Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.\n"
    s += ("Lemma tfib_img_cover0 : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= YImgTop.IMG_LO /\\ "
          "YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).\n"
          "Proof.\nintros ly S md LG. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. split.\n"
          "- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.\n"
          "- destruct (al_img _ _ _ _ LG AsanUbsan.AsanUbsan_segment_%03d ltac:(do %d right; left; reflexivity)) as [_ H]. "
          "cbn in H. lia.\nQed.\n") % (NSEG - 1, NSEG - 1)
    s += ("Lemma tfib_relro_img : forall a, 0x%x <= a < 0x%x -> in_img tfibsegs a.\n"
          "Proof.\nintros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].\n"
          "match goal with |- Z.le ?lo a /\\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in "
          "let h := eval vm_compute in sz in\nchange lo with l; change sz with h end. lia.\nQed.\n") % (RELRO_LO, RELRO_HI)
    s += ("#[global] Instance PB_tfib : PAImg lib_both3_0_listing := {|\n"
          "pa_segs := tfibsegs;\npa_tbl := tfibtbl_lib;\npa_tbl_ok := tfibtbl_lib_ok;\npa_val := tfib_val0;\n"
          "pa_sigma := tfib_sigma;\npa_cert := tfib_lib_check0;\n"
          "pa_B_ok := ltac:(unfold tfib_val0, tfib_B0; cbn; lia);\npa_val_range := tfib_val0_range;\n"
          "pa_wx := tfib_wx;\npa_segs_low := tfib_segs_low0;\npa_img_range := tfib_img_range0;\n"
          "pa_img_cover := tfib_img_cover0;\n"
          "pa_obj_img := ltac:(intros i Hi; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; "
          "do 13 (destruct i as [|i]; [unfold tfib_val0, tfib_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);\n"
          "pa_relro_lo := 0x%x;\npa_relro_hi := 0x%x;\npa_relro_img := tfib_relro_img |}.\n") % (RELRO_LO, RELRO_HI)
    s += ("Lemma both3_xcalls_ok : forall s k, In (s, k) both3_xcalls -> tfib_sigma s = tfib_val0 A_TEXT + k.\n"
          "Proof.\nintros s k H. cbn [both3_xcalls In] in H.\n"
          "repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]). destruct H.\nQed.\n"
          "#[global] Instance PX_tfib : PAXcalls lib_both3_0_listing := both3_xcalls_ok.\n"
          "Lemma tfib_obj_img_all : forall i, (i < tfib_nobj)%%nat -> YImgTop.IMG_LO <= tfib_val0 (A_OBJ i) /\\ "
          "tfib_val0 (A_OBJ i) + 8 <= YImgTop.IMG_TOP.\n"
          "Proof.\nintros i Hi. unfold tfib_nobj in Hi. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP.\n"
          "do %d (destruct i as [|i]; [unfold tfib_val0, tfib_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.\nQed.\n"
          "#[global] Instance PO_tfib : PAObjImg lib_both3_0_listing := tfib_obj_img_all.\n"
          "Lemma tfib_hi_img_all : forall j, (j < tfib_nhi)%%nat -> 0 <= tfib_val0 (A_HI j) /\\ "
          "tfib_val0 (A_HI j) < YImgTop.IMG_TOP.\n"
          "Proof.\nintros j Hj. unfold tfib_nhi in Hj. unfold YImgTop.IMG_TOP.\n"
          "do %d (destruct j as [|j]; [unfold tfib_val0, tfib_hi, A_OBJ, A_TEXT, A_HI; cbn; lia|]). exfalso; lia.\nQed.\n"
          "#[global] Instance PH_tfib : PAHiImg lib_both3_0_listing := tfib_hi_img_all.\nEnd c.\n") % (NOBJ, NHI)
    w("YCbj", s)


XC = sorted((n for n in m["funcs"] if n in {s for s, _ in m["syms"]}), key=lambda n: m["funcs"][n])


def yxcalls():
    s = ("From %s Require YZ00.\nFrom Stdlib Require Import ZArith NArith List Lia Bool.\n"
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.\n"
         "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.\n"
         "From %s Require Import YK11 YP0b YM05 YI0w YI0z YI12 YC4a.\nFrom %s Require YImgTop.\n"
         "Import ListNotations.\nOpen Scope Z_scope.\n") % (R, R, R)
    s += "Definition both3_xcalls : list (asym * Z) := [\n"
    s += ";\n".join("(AS_%s, AF_both3_%s)" % (ident(n), ident(n)) for n in XC) + " ].\n"
    s += ("Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.\n"
          "Class PAXcalls (L : ptable asym) {PI : PAImg L} : Prop :=\n"
          "pa_xcalls : forall s k, In (s, k) both3_xcalls -> pa_sigma s = pa_val A_TEXT + k.\n"
          "Class PAObjImg (L : ptable asym) {PI : PAImg L} : Prop :=\n"
          "pa_obj_img_all : forall i, (i < tfib_nobj)%nat -> YImgTop.IMG_LO <= pa_val (A_OBJ i) /\\ "
          "pa_val (A_OBJ i) + 8 <= YImgTop.IMG_TOP.\n"
          "Class PAHiImg (L : ptable asym) {PI : PAImg L} : Prop :=\n"
          "pa_hi_img : forall j, (j < tfib_nhi)%nat -> 0 <= pa_val (A_HI j) /\\ pa_val (A_HI j) < YImgTop.IMG_TOP.\n"
          "Section c.\nContext {L : ptable asym} {PI : PAImg L} {PX : PAXcalls L}.\n")
    for n in XC:
        i = ident(n)
        s += ("Lemma pa_sigma_%s : pa_sigma AS_%s = pa_val A_TEXT + AF_both3_%s.\n"
              "Proof. apply pa_xcalls. cbn [In both3_xcalls]. repeat (first [left; reflexivity | right]). Qed.\n"
              % (i, i, i))
    s += "End c.\nEnd b.\n"
    w("YXcalls", s)


for f in (yi0w, yi0z, yb1v, ycef, yi12, yc8i, ycbj, yxcalls):
    f()
print("YI0w YI0z YB1v YCef YI12 YC8i YCbj YXcalls written: %d syms, %d slots, %d funcs, %d objs, %d his, %d xcalls"
      % (len(m["syms"]), m["nslots"], len(m["funcs"]), NOBJ, NHI, len(XC)))
