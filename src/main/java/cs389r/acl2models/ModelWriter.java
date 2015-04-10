package cs389r.acl2models;

import com.github.mustachejava.DefaultMustacheFactory;
import com.github.mustachejava.Mustache;
import com.github.mustachejava.MustacheFactory;
import com.sun.tools.internal.ws.processor.model.Model;
import cs389r.Main;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by colestewart on 4/8/15.
 */
public class ModelWriter {

    private interface ModelPiece {
        public void write(OutputStream stream) throws IOException;
    }

    private final List<ModelPiece> modelPieces;

    private final OutputStream stream;

    public ModelWriter(OutputStream stream) {
        this.stream = stream;
        this.modelPieces = new ArrayList<>();
    }

    public void writePieces() throws IOException {
        for (ModelPiece piece : modelPieces) {
            piece.write(stream);
        }
        stream.flush();
        stream.close();
    }

    public void addModelPiece(String piece) {
        modelPieces.add(s -> {
            s.write(piece.getBytes(Charset.defaultCharset()));
        });
    }

    public void addModelPiece(File f) {
        modelPieces.add(s -> {
            BufferedReader reader = new BufferedReader(new FileReader(f));
            String line;
            while ((line = reader.readLine()) != null) {
                s.write((line + '\n').getBytes(Charset.defaultCharset()));
            }
            reader.close();
        });
    }

    public void addModelPiece(InputStream in) {
        modelPieces.add(s -> {
            BufferedReader reader = new BufferedReader(new InputStreamReader(in, "UTF-8"));
            String line;
            while ((line = reader.readLine()) != null) {
                s.write((line + '\n').getBytes(Charset.defaultCharset()));
            }
            reader.close();
        });
    }


    public void addModelPieceFromTemplate(String templateName, Map<String, Object> scopes) {
        String templatePath = "models/" + templateName;

        modelPieces.add(s -> {
            Writer w = new OutputStreamWriter(stream);
            MustacheFactory mf = new DefaultMustacheFactory();
            InputStream templateStream = Main.class.getClassLoader().getResourceAsStream(templatePath);
            Mustache mustache = mf.compile(new InputStreamReader(templateStream), templateName);
            mustache.execute(w, scopes);
            w.flush();
            templateStream.close();
        });
    }

}
