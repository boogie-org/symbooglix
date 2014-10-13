﻿using System;
using System.IO;
using System.CodeDom.Compiler;
using System.Diagnostics;

namespace Symbooglix
{
    public class ExecutionTreePrinter
    {
        ExecutionTreeNode Root;
        int Indent;
        public ExecutionTreePrinter(ExecutionTreeNode root, int indent=2)
        {
            Debug.Assert(indent >= 0, "Indent cannot be negative");
            Debug.Assert(root != null, "root cannot be null");
            this.Root = root;
            this.Indent = indent;
        }

        protected virtual void PrintPreamble(TextWriter TW)
        {
            TW.WriteLine("/* Generated by Symbooglix */");
        }

        protected virtual void PrintStartGraph(TextWriter TW)
        {
            TW.WriteLine("digraph \"Execution Tree\"");
            TW.WriteLine("{");
            PushIndent(TW);
        }

        protected virtual void PrintCloseGraph(TextWriter TW)
        {
            PopIndent(TW);
            TW.WriteLine("}");
        }

        protected void PushIndent(TextWriter TW)
        {
            if (TW is IndentedTextWriter)
            {
                ( TW as IndentedTextWriter ).Indent += this.Indent;
            }
        }

        protected void PopIndent(TextWriter TW)
        {
            if (TW is IndentedTextWriter)
            {
                ( TW as IndentedTextWriter ).Indent -= this.Indent;
            }
        }

        protected virtual void PrintNode(TextWriter TW, ExecutionTreeNode node)
        {
            // Declare node
            TW.Write("{0} [", GetNodeID(node));

            // Write node attributes
            TW.Write(GetNodeAttributes(node));

            TW.WriteLine("];");

            if (node.ChildrenCount == 0)
                return;

            // Visit Children
            for (int index = 0; index < node.ChildrenCount; ++index)
                PrintNode(TW, node.GetChild(index));

            // Write edges. We can do this now because all child nodes have been declared
            TW.WriteLine("");
            for (int index = 0; index < node.ChildrenCount; ++index)
            {
                TW.WriteLine("{0} -> {1};", GetNodeID(node), GetNodeID(node.GetChild(index)));
            }
        }

        protected virtual string GetNodeID(ExecutionTreeNode node)
        {
            var id = string.Format("S{0}_{1}", (node.State.Id <0)?("m" + (node.State.Id*-1).ToString()):node.State.Id.ToString(), node.Depth);

            if (node.ChildrenCount == 0)
                id += "_term";
            return id;
        }

        protected virtual string GetNodeAttributes(ExecutionTreeNode node)
        {
            var attr = string.Format("shape=record,label=\"{0}", GetNodeID(node));

            if (node.CreatedAt != null)
                attr += string.Format("\\n{0}:{1}", node.CreatedAt.LineNumber, node.CreatedAt.ToString());

            if (node.ChildrenCount == 0)
            {
                attr += "\\nTermination:" + EscapeLabelText(node.State.TerminationType.GetMessage());
            }

            // Close label
            attr += "\"";

            if (node.ChildrenCount == 0)
            {
                attr += ",style=filled, fillcolor=";
                if (node.State.TerminationType is TerminatedWithoutError)
                    attr += "\"green\"";
                else
                    attr += "\"red\"";
            }

            return attr;
        }

        protected string EscapeLabelText(string input)
        {
            var temp = input.Replace(">","\\>");
            temp = temp.Replace("<", "\\<");
            temp = temp.Replace("{", "\\{");
            temp = temp.Replace("}", "\\}");
            return temp;
        }
            
        public void Print(TextWriter TW)
        {
            TextWriter ITW = TW;
            if (this.Indent > 0)
            {
                ITW = new IndentedTextWriter(TW);
            }

            PrintPreamble(ITW);
            PrintStartGraph(ITW);

            PrintNode(ITW, this.Root);

            PrintCloseGraph(ITW);
        }
    }
}

